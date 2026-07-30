module CilFrontend.StackSim

open System
open System.Collections.Generic
open Mono.Cecil
open Mono.Cecil.Cil

/// KoATの整数更新として扱う算術式。
type IntExpr =
    | Const of int
    | Var of string
    | BinOp of string * IntExpr * IntExpr

/// 遷移のガードとしてだけ扱う論理式。
type BoolExpr =
    | Compare of string * IntExpr * IntExpr
    | NonZero of IntExpr
    | BoolNot of BoolExpr
    | BoolOr of BoolExpr * BoolExpr

/// CILではBooleanも評価スタック上の値なので、スタック層では両者を保持する。
type StackValue =
    | IntValue of IntExpr
    | BoolValue of BoolExpr

let rec renderIntExpr expression =
    match expression with
    | Const n -> string n
    | Var name -> name
    | BinOp (op, left, right) ->
        sprintf "(%s %s %s)" (renderIntExpr left) op (renderIntExpr right)

let rec renderBoolExpr expression =
    match expression with
    | Compare (op, left, right) ->
        sprintf "(%s %s %s)" (renderIntExpr left) op (renderIntExpr right)
    | NonZero value -> sprintf "(%s != 0)" (renderIntExpr value)
    | BoolNot inner -> sprintf "!(%s)" (renderBoolExpr inner)
    | BoolOr (left, right) ->
        sprintf "(%s || %s)" (renderBoolExpr left) (renderBoolExpr right)

let renderStackValue value =
    match value with
    | IntValue expression -> renderIntExpr expression
    | BoolValue expression -> renderBoolExpr expression

type Command = { Target: string; Value: StackValue }

let renderCommand command =
    sprintf "%s = %s" command.Target (renderStackValue command.Value)

let private argName (method: MethodDefinition) index =
    if method.HasThis then
        if index = 0 then "this"
        else method.Parameters.[index - 1].Name
    else method.Parameters.[index].Name

let private parameterName (parameter: ParameterDefinition) =
    if String.IsNullOrWhiteSpace parameter.Name then sprintf "arg%d" parameter.Index
    else parameter.Name

let private localName (variable: VariableDefinition) = sprintf "loc%d" variable.Index

type SimulationResult = {
    Commands: Command list
    Guard: BoolExpr option
    SwitchValue: IntExpr option
    /// スタックの底から先頭の順
    ExitStack: StackValue list
}

let simulateBlock
    (method: MethodDefinition)
    (initialStack: StackValue list)
    (instructions: Instruction list)
    : SimulationResult =

    let stack = Stack<StackValue>()
    for value in initialStack do stack.Push value

    let commands = ResizeArray<Command>()
    let environment = Dictionary<string, StackValue>()
    let mutable guard = None
    let mutable switchValue = None
    let mutable currentInstruction: Instruction option = None

    let instructionText () =
        match currentInstruction with
        | Some instruction -> sprintf "IL_%04X (%s)" instruction.Offset instruction.OpCode.Name
        | None -> "不明な命令"

    let pop purpose =
        if stack.Count = 0 then
            failwithf
                "評価スタックが不足しています: %s で%sに必要な値がありません。"
                (instructionText ())
                purpose
        stack.Pop()

    let popInt purpose =
        match pop purpose with
        | IntValue expression -> expression
        | BoolValue _ ->
            failwithf "%s でBoolean値を整数式として使用することはできません。" (instructionText ())

    let toBool value =
        match value with
        | BoolValue expression -> expression
        | IntValue expression -> NonZero expression

    let peek purpose =
        if stack.Count = 0 then
            failwithf
                "評価スタックが不足しています: %s で%sに必要な値がありません。"
                (instructionText ())
                purpose
        stack.Peek()

    let readVariable name =
        match environment.TryGetValue name with
        | true, value -> value
        | false, _ -> IntValue(Var name)

    let writeVariable name value =
        environment.[name] <- value
        commands.Add({ Target = name; Value = value })

    let popArithmetic op =
        let right = popInt (sprintf "演算 %s の右辺" op)
        let left = popInt (sprintf "演算 %s の左辺" op)
        stack.Push(IntValue(BinOp(op, left, right)))

    let popComparison op =
        let right = popInt (sprintf "比較 %s の右辺" op)
        let left = popInt (sprintf "比較 %s の左辺" op)
        Compare(op, left, right)

    let popUnsignedGreater () =
        let right = popInt "符号なし比較の右辺"
        let left = popInt "符号なし比較の左辺"
        match right with
        | Const 0 -> Compare("!=", left, right)
        | _ -> Compare(">u", left, right)

    for instr in instructions do
        currentInstruction <- Some instr
        match instr.OpCode.Code with
        | Code.Nop -> ()
        | Code.Ldarg_0 -> stack.Push(readVariable (argName method 0))
        | Code.Ldarg_1 -> stack.Push(readVariable (argName method 1))
        | Code.Ldarg_2 -> stack.Push(readVariable (argName method 2))
        | Code.Ldarg_3 -> stack.Push(readVariable (argName method 3))
        | Code.Ldarg | Code.Ldarg_S ->
            let parameter = instr.Operand :?> ParameterDefinition
            stack.Push(readVariable (parameterName parameter))
        | Code.Starg | Code.Starg_S ->
            let parameter = instr.Operand :?> ParameterDefinition
            writeVariable (parameterName parameter) (pop "引数への代入")

        | Code.Ldc_I4_M1 -> stack.Push(IntValue(Const -1))
        | Code.Ldc_I4_0 -> stack.Push(IntValue(Const 0))
        | Code.Ldc_I4_1 -> stack.Push(IntValue(Const 1))
        | Code.Ldc_I4_2 -> stack.Push(IntValue(Const 2))
        | Code.Ldc_I4_3 -> stack.Push(IntValue(Const 3))
        | Code.Ldc_I4_4 -> stack.Push(IntValue(Const 4))
        | Code.Ldc_I4_5 -> stack.Push(IntValue(Const 5))
        | Code.Ldc_I4_6 -> stack.Push(IntValue(Const 6))
        | Code.Ldc_I4_7 -> stack.Push(IntValue(Const 7))
        | Code.Ldc_I4_8 -> stack.Push(IntValue(Const 8))
        | Code.Ldc_I4_S -> stack.Push(IntValue(Const(int (instr.Operand :?> sbyte))))
        | Code.Ldc_I4 -> stack.Push(IntValue(Const(instr.Operand :?> int)))

        | Code.Ldloc_0 -> stack.Push(readVariable "loc0")
        | Code.Ldloc_1 -> stack.Push(readVariable "loc1")
        | Code.Ldloc_2 -> stack.Push(readVariable "loc2")
        | Code.Ldloc_3 -> stack.Push(readVariable "loc3")
        | Code.Ldloc | Code.Ldloc_S ->
            let variable = instr.Operand :?> VariableDefinition
            stack.Push(readVariable (localName variable))
        | Code.Stloc_0 -> writeVariable "loc0" (pop "ローカル変数への代入")
        | Code.Stloc_1 -> writeVariable "loc1" (pop "ローカル変数への代入")
        | Code.Stloc_2 -> writeVariable "loc2" (pop "ローカル変数への代入")
        | Code.Stloc_3 -> writeVariable "loc3" (pop "ローカル変数への代入")
        | Code.Stloc | Code.Stloc_S ->
            let variable = instr.Operand :?> VariableDefinition
            writeVariable (localName variable) (pop "ローカル変数への代入")

        | Code.Add -> popArithmetic "+"
        | Code.Sub -> popArithmetic "-"
        | Code.Mul -> popArithmetic "*"
        | Code.Div | Code.Div_Un -> popArithmetic "/"
        | Code.Rem | Code.Rem_Un -> popArithmetic "%"
        | Code.Cgt -> stack.Push(BoolValue(popComparison ">"))
        | Code.Cgt_Un -> stack.Push(BoolValue(popUnsignedGreater ()))
        | Code.Clt -> stack.Push(BoolValue(popComparison "<"))
        | Code.Clt_Un -> stack.Push(BoolValue(popComparison "<u"))
        | Code.Ceq -> stack.Push(BoolValue(popComparison "=="))
        | Code.Neg ->
            stack.Push(IntValue(BinOp("-", Const 0, popInt "符号反転")))
        | Code.Dup -> stack.Push(peek "dup")
        | Code.Pop -> pop "pop" |> ignore

        | Code.Brtrue | Code.Brtrue_S | Code.Brfalse | Code.Brfalse_S ->
            guard <- Some(toBool (pop "条件分岐"))
        | Code.Beq | Code.Beq_S -> guard <- Some(popComparison "==")
        | Code.Bne_Un | Code.Bne_Un_S -> guard <- Some(popComparison "!=")
        | Code.Bgt | Code.Bgt_S -> guard <- Some(popComparison ">")
        | Code.Bgt_Un | Code.Bgt_Un_S -> guard <- Some(popComparison ">u")
        | Code.Bge | Code.Bge_S -> guard <- Some(popComparison ">=")
        | Code.Bge_Un | Code.Bge_Un_S -> guard <- Some(popComparison ">=u")
        | Code.Blt | Code.Blt_S -> guard <- Some(popComparison "<")
        | Code.Blt_Un | Code.Blt_Un_S -> guard <- Some(popComparison "<u")
        | Code.Ble | Code.Ble_S -> guard <- Some(popComparison "<=")
        | Code.Ble_Un | Code.Ble_Un_S -> guard <- Some(popComparison "<=u")

        | Code.Switch -> switchValue <- Some(popInt "switch")
        | Code.Br | Code.Br_S | Code.Ret -> ()
        | other ->
            failwithf
                "未対応の命令です(このプロトタイプの対象外): IL_%04X (%O)"
                instr.Offset
                other

    {
        Commands = List.ofSeq commands
        Guard = guard
        SwitchValue = switchValue
        ExitStack = stack.ToArray() |> Array.rev |> List.ofArray
    }
