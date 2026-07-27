module CilFrontend.StackSim

open System
open System.Collections.Generic
open Mono.Cecil
open Mono.Cecil.Cil

/// スタック上に積まれる「まだ変数に代入されていない式」を表す簡易AST
type Expr =
    | Const of int
    | Var of string
    | BinOp of string * Expr * Expr
    | Not of Expr

let rec renderExpr (e: Expr) =
    match e with
    | Const n -> string n
    | Var name -> name
    | BinOp (op, a, b) -> sprintf "(%s %s %s)" (renderExpr a) op (renderExpr b)
    | Not inner -> sprintf "!(%s)" (renderExpr inner)

type Command = { Target: string; Value: Expr }

let renderCommand (c: Command) = sprintf "%s = %s" c.Target (renderExpr c.Value)

let private argName (method: MethodDefinition) (index: int) =
    if method.HasThis then
        if index = 0 then "this"
        else method.Parameters.[index - 1].Name
    else
        method.Parameters.[index].Name

let private parameterName (parameter: ParameterDefinition) =
    if String.IsNullOrWhiteSpace parameter.Name then
        sprintf "arg%d" parameter.Index
    else
        parameter.Name

let private localName (variable: VariableDefinition) = sprintf "loc%d" variable.Index

type SimulationResult = {
    Commands: Command list
    Guard: Expr option
    SwitchValue: Expr option
    /// スタックの底から先頭の順
    ExitStack: Expr list
}

/// 1つの基本ブロックをシミュレーションする。
/// initialStackを受け取るため、CFGをまたぐ評価スタックも扱える。
let simulateBlock
    (method: MethodDefinition)
    (initialStack: Expr list)
    (instructions: Instruction list)
    : SimulationResult =

    let stack = Stack<Expr>()
    for value in initialStack do
        stack.Push value

    let commands = ResizeArray<Command>()
    let environment = Dictionary<string, Expr>()
    let mutable guard: Expr option = None
    let mutable switchValue: Expr option = None

    let readVariable name =
        match environment.TryGetValue name with
        | true, value -> value
        | false, _ -> Var name

    let writeVariable name value =
        environment.[name] <- value
        commands.Add({ Target = name; Value = value })

    let pop2AndPush op =
        let b = stack.Pop()
        let a = stack.Pop()
        stack.Push(BinOp(op, a, b))

    let popComparison op =
        let b = stack.Pop()
        let a = stack.Pop()
        BinOp(op, a, b)

    let popUnsignedGreater () =
        let b = stack.Pop()
        let a = stack.Pop()

        // C#コンパイラは整数の x != 0 を
        //   ldarg x; ldc.i4.0; cgt.un
        // として出力する。符号なし表現では非0値がすべて0より大きいため、
        // この形は数学的整数上の x != 0 として正確に正規化できる。
        match b with
        | Const 0 -> BinOp("!=", a, b)
        | _ -> BinOp(">u", a, b)

    for instr in instructions do
        match instr.OpCode.Code with
        | Code.Nop -> ()

        // 引数
        | Code.Ldarg_0 -> stack.Push(readVariable (argName method 0))
        | Code.Ldarg_1 -> stack.Push(readVariable (argName method 1))
        | Code.Ldarg_2 -> stack.Push(readVariable (argName method 2))
        | Code.Ldarg_3 -> stack.Push(readVariable (argName method 3))
        | Code.Ldarg
        | Code.Ldarg_S ->
            let parameter = instr.Operand :?> ParameterDefinition
            stack.Push(readVariable (parameterName parameter))
        | Code.Starg
        | Code.Starg_S ->
            let parameter = instr.Operand :?> ParameterDefinition
            writeVariable (parameterName parameter) (stack.Pop())

        // int32定数
        | Code.Ldc_I4_M1 -> stack.Push(Const -1)
        | Code.Ldc_I4_0 -> stack.Push(Const 0)
        | Code.Ldc_I4_1 -> stack.Push(Const 1)
        | Code.Ldc_I4_2 -> stack.Push(Const 2)
        | Code.Ldc_I4_3 -> stack.Push(Const 3)
        | Code.Ldc_I4_4 -> stack.Push(Const 4)
        | Code.Ldc_I4_5 -> stack.Push(Const 5)
        | Code.Ldc_I4_6 -> stack.Push(Const 6)
        | Code.Ldc_I4_7 -> stack.Push(Const 7)
        | Code.Ldc_I4_8 -> stack.Push(Const 8)
        | Code.Ldc_I4_S -> stack.Push(Const(int (instr.Operand :?> sbyte)))
        | Code.Ldc_I4 -> stack.Push(Const(instr.Operand :?> int))

        // ローカル変数
        | Code.Ldloc_0 -> stack.Push(readVariable "loc0")
        | Code.Ldloc_1 -> stack.Push(readVariable "loc1")
        | Code.Ldloc_2 -> stack.Push(readVariable "loc2")
        | Code.Ldloc_3 -> stack.Push(readVariable "loc3")
        | Code.Ldloc
        | Code.Ldloc_S ->
            let variable = instr.Operand :?> VariableDefinition
            stack.Push(readVariable (localName variable))
        | Code.Stloc_0 -> writeVariable "loc0" (stack.Pop())
        | Code.Stloc_1 -> writeVariable "loc1" (stack.Pop())
        | Code.Stloc_2 -> writeVariable "loc2" (stack.Pop())
        | Code.Stloc_3 -> writeVariable "loc3" (stack.Pop())
        | Code.Stloc
        | Code.Stloc_S ->
            let variable = instr.Operand :?> VariableDefinition
            writeVariable (localName variable) (stack.Pop())

        // 算術・比較
        | Code.Add -> pop2AndPush "+"
        | Code.Sub -> pop2AndPush "-"
        | Code.Mul -> pop2AndPush "*"
        | Code.Div
        | Code.Div_Un -> pop2AndPush "/"
        | Code.Rem
        | Code.Rem_Un -> pop2AndPush "%"
        | Code.Cgt -> pop2AndPush ">"
        | Code.Cgt_Un -> stack.Push(popUnsignedGreater ())
        | Code.Clt -> pop2AndPush "<"
        | Code.Clt_Un -> pop2AndPush "<u"
        | Code.Ceq -> pop2AndPush "=="
        | Code.Neg -> stack.Push(BinOp("-", Const 0, stack.Pop()))
        | Code.Dup -> stack.Push(stack.Peek())
        | Code.Pop -> stack.Pop() |> ignore

        // スタック値の真偽による条件分岐
        | Code.Brtrue
        | Code.Brtrue_S
        | Code.Brfalse
        | Code.Brfalse_S ->
            guard <- Some(stack.Pop())

        // 2値を直接比較する条件分岐
        | Code.Beq
        | Code.Beq_S -> guard <- Some(popComparison "==")
        | Code.Bne_Un
        | Code.Bne_Un_S -> guard <- Some(popComparison "!=")
        | Code.Bgt
        | Code.Bgt_S -> guard <- Some(popComparison ">")
        | Code.Bgt_Un
        | Code.Bgt_Un_S -> guard <- Some(popComparison ">u")
        | Code.Bge
        | Code.Bge_S -> guard <- Some(popComparison ">=")
        | Code.Bge_Un
        | Code.Bge_Un_S -> guard <- Some(popComparison ">=u")
        | Code.Blt
        | Code.Blt_S -> guard <- Some(popComparison "<")
        | Code.Blt_Un
        | Code.Blt_Un_S -> guard <- Some(popComparison "<u")
        | Code.Ble
        | Code.Ble_S -> guard <- Some(popComparison "<=")
        | Code.Ble_Un
        | Code.Ble_Un_S -> guard <- Some(popComparison "<=u")

        | Code.Switch -> switchValue <- Some(stack.Pop())
        | Code.Br
        | Code.Br_S
        | Code.Ret -> ()

        | other -> failwithf "未対応の命令です(このプロトタイプの対象外): %O" other

    {
        Commands = List.ofSeq commands
        Guard = guard
        SwitchValue = switchValue
        ExitStack = stack.ToArray() |> Array.rev |> List.ofArray
    }
