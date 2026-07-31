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
    /// 文字列そのものではなく、KoATで追跡する長さを保持する。
    | StringValue of length: IntExpr
    /// リストそのものではなく、KoATで追跡する残り要素数を保持する。
    | ListValue of length: IntExpr
    /// System.Collections.Generic.List<T>そのものではなく要素数を保持する。
    | GenericListValue of length: IntExpr
    /// 配列そのものではなく要素数を保持する。
    | ArrayValue of length: IntExpr
    /// List<T>.Enumeratorの未走査要素数を保持する。
    | ListEnumeratorValue of remaining: IntExpr
    /// foreachのCurrent。要素値に依存しない走査だけを許可するための印。
    | UnknownElementValue
    /// 値型Enumeratorへのldloca。MoveNextで元のローカルを更新する。
    | LocalAddress of name: string
    /// null判定を扱うための値。空文字列・空リストとは同一視しない。
    | NullValue

let isStringType (t: TypeReference) =
    t.FullName = "System.String"

let isListType (t: TypeReference) =
    t.FullName.StartsWith("Microsoft.FSharp.Collections.FSharpList`1", StringComparison.Ordinal)

let isGenericListType (t: TypeReference) =
    t.FullName.StartsWith("System.Collections.Generic.List`1", StringComparison.Ordinal)
    && not (t.FullName.Contains("/Enumerator", StringComparison.Ordinal))

let isGenericListEnumeratorType (t: TypeReference) =
    t.FullName.StartsWith("System.Collections.Generic.List`1/Enumerator", StringComparison.Ordinal)

let isArrayType (t: TypeReference) = t.IsArray

let sizeVariableName name = name + "_length"

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
    | StringValue length -> sprintf "string(length=%s)" (renderIntExpr length)
    | ListValue length -> sprintf "list(length=%s)" (renderIntExpr length)
    | GenericListValue length -> sprintf "List<T>(count=%s)" (renderIntExpr length)
    | ArrayValue length -> sprintf "array(length=%s)" (renderIntExpr length)
    | ListEnumeratorValue remaining -> sprintf "List<T>.Enumerator(remaining=%s)" (renderIntExpr remaining)
    | UnknownElementValue -> "foreach-element"
    | LocalAddress name -> sprintf "&%s" name
    | NullValue -> "null"

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
        | StringValue _ | ListValue _ | GenericListValue _ | ArrayValue _ | ListEnumeratorValue _
        | UnknownElementValue | LocalAddress _ | NullValue ->
            failwithf "%s で参照値を整数式として使用することはできません。" (instructionText ())

    let toBool value =
        match value with
        | BoolValue expression -> expression
        | IntValue expression -> NonZero expression
        | StringValue _ ->
            failwithf
                "%s で参照値のnull判定を長さ判定へ置き換えることはできません。"
                (instructionText ())
        // F#リストは空リストをnullで表すため、非null判定は非空判定と一致する。
        | ListValue length -> NonZero length
        | GenericListValue _ | ArrayValue _ | ListEnumeratorValue _ | UnknownElementValue | LocalAddress _ ->
            failwithf "%s でこの参照値を条件として使用することはできません。" (instructionText ())
        | NullValue -> Compare("!=", Const 0, Const 0)

    let peek purpose =
        if stack.Count = 0 then
            failwithf
                "評価スタックが不足しています: %s で%sに必要な値がありません。"
                (instructionText ())
                purpose
        stack.Peek()

    let initialValue name (variableType: TypeReference) =
        if isStringType variableType then StringValue(Var(sizeVariableName name))
        elif isListType variableType then ListValue(Var(sizeVariableName name))
        elif isGenericListType variableType then GenericListValue(Var(sizeVariableName name))
        elif isArrayType variableType then ArrayValue(Var(sizeVariableName name))
        elif isGenericListEnumeratorType variableType then
            ListEnumeratorValue(Var(name + "_remaining"))
        else IntValue(Var name)

    let readVariable name variableType =
        match environment.TryGetValue name with
        | true, value -> value
        | false, _ -> initialValue name variableType

    let writeVariable name variableType value =
        let storedValue, command =
            if isStringType variableType then
                match value with
                | StringValue length ->
                    StringValue length, Some { Target = sizeVariableName name; Value = IntValue length }
                | NullValue ->
                    failwithf
                        "%s でnullを文字列変数 %s へ代入する処理は長さだけでは表現できません。"
                        (instructionText ())
                        name
                | _ ->
                    failwithf "%s で文字列変数 %s へ非文字列値を代入できません。" (instructionText ()) name
            elif isListType variableType then
                match value with
                | ListValue length ->
                    ListValue length, Some { Target = sizeVariableName name; Value = IntValue length }
                // FSharpListはUseNullAsTrueValueであり、nullは空リストを表す。
                | NullValue ->
                    ListValue(Const 0), Some { Target = sizeVariableName name; Value = IntValue(Const 0) }
                | _ ->
                    failwithf "%s でリスト変数 %s へ非リスト値を代入できません。" (instructionText ()) name
            elif isGenericListType variableType then
                match value with
                | GenericListValue length ->
                    GenericListValue length, Some { Target = sizeVariableName name; Value = IntValue length }
                | NullValue ->
                    failwithf "%s でnullをList<T>変数 %s へ代入する処理は要素数だけでは表現できません。" (instructionText ()) name
                | _ -> failwithf "%s でList<T>変数 %s へ不正な値を代入できません。" (instructionText ()) name
            elif isArrayType variableType then
                match value with
                | ArrayValue length ->
                    ArrayValue length, Some { Target = sizeVariableName name; Value = IntValue length }
                | NullValue ->
                    failwithf "%s でnullを配列変数 %s へ代入する処理は長さだけでは表現できません。" (instructionText ()) name
                | _ -> failwithf "%s で配列変数 %s へ不正な値を代入できません。" (instructionText ()) name
            elif isGenericListEnumeratorType variableType then
                match value with
                | ListEnumeratorValue remaining ->
                    ListEnumeratorValue remaining, Some { Target = name + "_remaining"; Value = IntValue remaining }
                | _ -> failwithf "%s でList<T>.Enumerator変数 %s へ不正な値を代入できません。" (instructionText ()) name
            else
                match value with
                | UnknownElementValue -> UnknownElementValue, None
                | _ -> value, Some { Target = name; Value = value }

        environment.[name] <- storedValue
        command |> Option.iter commands.Add

    let argumentType index =
        if method.HasThis then
            if index = 0 then method.DeclaringType :> TypeReference
            else method.Parameters.[index - 1].ParameterType
        else
            method.Parameters.[index].ParameterType

    let localAt index = method.Body.Variables.[index]

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

    let popCallArguments count =
        [ for index in 1 .. count -> pop (sprintf "呼び出し引数 %d" index) ]
        |> List.rev

    let handleCall (called: MethodReference) =
        let arguments = popCallArguments called.Parameters.Count
        let receiver =
            if called.HasThis then Some(pop "インスタンスメソッドのレシーバー")
            else None

        match called.DeclaringType.FullName, called.Name, receiver, arguments with
        | "System.String", "get_Length", Some(StringValue length), [] ->
            stack.Push(IntValue length)
        | "System.String", "IsNullOrEmpty", None, [ StringValue length ] ->
            stack.Push(BoolValue(Compare("==", length, Const 0)))
        | "System.String", "IsNullOrEmpty", None, [ NullValue ] ->
            stack.Push(BoolValue(Compare("==", Const 0, Const 0)))
        | declaringType, "get_Length", Some(ListValue length), []
            when declaringType.StartsWith(
                "Microsoft.FSharp.Collections.FSharpList`1",
                StringComparison.Ordinal) ->
            stack.Push(IntValue length)
        | declaringType, "get_IsEmpty", Some(ListValue length), []
            when declaringType.StartsWith(
                "Microsoft.FSharp.Collections.FSharpList`1",
                StringComparison.Ordinal) ->
            stack.Push(BoolValue(Compare("==", length, Const 0)))
        | declaringType, ("get_Tail" | "get_TailOrNull"), Some(ListValue length), []
            when declaringType.StartsWith(
                "Microsoft.FSharp.Collections.FSharpList`1",
                StringComparison.Ordinal) ->
            stack.Push(ListValue(BinOp("-", length, Const 1)))
        | "Microsoft.FSharp.Collections.ListModule", "Length", None, [ ListValue length ] ->
            stack.Push(IntValue length)
        | declaringType, "get_Count", Some(GenericListValue length), []
            when declaringType.StartsWith("System.Collections.Generic.List`1", StringComparison.Ordinal) ->
            stack.Push(IntValue length)
        | declaringType, "GetEnumerator", Some(GenericListValue length), []
            when declaringType.StartsWith("System.Collections.Generic.List`1", StringComparison.Ordinal) ->
            stack.Push(ListEnumeratorValue length)
        | declaringType, "MoveNext", Some(LocalAddress name), []
            when declaringType.StartsWith("System.Collections.Generic.List`1/Enumerator", StringComparison.Ordinal) ->
            let variable = localAt (Int32.Parse(name.Substring(3)))
            match readVariable name variable.VariableType with
            | ListEnumeratorValue remaining ->
                let next = BinOp("-", remaining, Const 1)
                environment.[name] <- ListEnumeratorValue next
                commands.Add { Target = name + "_remaining"; Value = IntValue next }
                stack.Push(BoolValue(Compare(">", remaining, Const 0)))
            | _ -> failwithf "%s のEnumerator状態が不正です。" (instructionText ())
        | declaringType, "get_Current", Some(LocalAddress _), []
            when declaringType.StartsWith("System.Collections.Generic.List`1/Enumerator", StringComparison.Ordinal) ->
            stack.Push UnknownElementValue
        | _, "Dispose", Some(LocalAddress _), [] -> ()
        | _ ->
            failwithf
                "未対応の呼び出しです: %s（string/listは長さを取得・更新できる操作だけに対応しています。）"
                called.FullName

    for instr in instructions do
        currentInstruction <- Some instr
        match instr.OpCode.Code with
        | Code.Nop -> ()
        | Code.Ldarg_0 -> stack.Push(readVariable (argName method 0) (argumentType 0))
        | Code.Ldarg_1 -> stack.Push(readVariable (argName method 1) (argumentType 1))
        | Code.Ldarg_2 -> stack.Push(readVariable (argName method 2) (argumentType 2))
        | Code.Ldarg_3 -> stack.Push(readVariable (argName method 3) (argumentType 3))
        | Code.Ldarg | Code.Ldarg_S ->
            let parameter = instr.Operand :?> ParameterDefinition
            stack.Push(readVariable (parameterName parameter) parameter.ParameterType)
        | Code.Starg | Code.Starg_S ->
            let parameter = instr.Operand :?> ParameterDefinition
            writeVariable
                (parameterName parameter)
                parameter.ParameterType
                (pop "引数への代入")

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

        | Code.Ldstr ->
            let value = instr.Operand :?> string
            stack.Push(StringValue(Const value.Length))
        | Code.Ldnull -> stack.Push NullValue
        | Code.Newarr ->
            let length = popInt "配列の長さ"
            stack.Push(ArrayValue length)
        | Code.Ldlen ->
            match pop "配列のLength" with
            | ArrayValue length -> stack.Push(IntValue length)
            | _ -> failwithf "%s のldlenに配列以外の値が渡されました。" (instructionText ())
        | Code.Ldelem_I | Code.Ldelem_I1 | Code.Ldelem_U1
        | Code.Ldelem_I2 | Code.Ldelem_U2 | Code.Ldelem_I4
        | Code.Ldelem_U4 | Code.Ldelem_I8 | Code.Ldelem_R4
        | Code.Ldelem_R8 | Code.Ldelem_Ref | Code.Ldelem_Any ->
            popInt "配列の添字" |> ignore
            match pop "配列要素の読み取り" with
            | ArrayValue _ -> stack.Push UnknownElementValue
            | _ -> failwithf "%s のldelemに配列以外の値が渡されました。" (instructionText ())
        | Code.Stelem_I | Code.Stelem_I1 | Code.Stelem_I2 | Code.Stelem_I4
        | Code.Stelem_I8 | Code.Stelem_R4 | Code.Stelem_R8 | Code.Stelem_Ref
        | Code.Stelem_Any ->
            failwithf "%s の配列要素への書き込みは未対応です。" (instructionText ())

        | Code.Ldloc_0 -> stack.Push(readVariable "loc0" (localAt 0).VariableType)
        | Code.Ldloc_1 -> stack.Push(readVariable "loc1" (localAt 1).VariableType)
        | Code.Ldloc_2 -> stack.Push(readVariable "loc2" (localAt 2).VariableType)
        | Code.Ldloc_3 -> stack.Push(readVariable "loc3" (localAt 3).VariableType)
        | Code.Ldloc | Code.Ldloc_S ->
            let variable = instr.Operand :?> VariableDefinition
            stack.Push(readVariable (localName variable) variable.VariableType)
        | Code.Ldloca | Code.Ldloca_S ->
            let variable = instr.Operand :?> VariableDefinition
            stack.Push(LocalAddress(localName variable))
        | Code.Stloc_0 -> writeVariable "loc0" (localAt 0).VariableType (pop "ローカル変数への代入")
        | Code.Stloc_1 -> writeVariable "loc1" (localAt 1).VariableType (pop "ローカル変数への代入")
        | Code.Stloc_2 -> writeVariable "loc2" (localAt 2).VariableType (pop "ローカル変数への代入")
        | Code.Stloc_3 -> writeVariable "loc3" (localAt 3).VariableType (pop "ローカル変数への代入")
        | Code.Stloc | Code.Stloc_S ->
            let variable = instr.Operand :?> VariableDefinition
            writeVariable
                (localName variable)
                variable.VariableType
                (pop "ローカル変数への代入")

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
        | Code.Conv_I4 -> stack.Push(IntValue(popInt "Int32への変換"))
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
        | Code.Call | Code.Callvirt ->
            handleCall (instr.Operand :?> MethodReference)
        | Code.Constrained -> ()
        | Code.Br | Code.Br_S | Code.Leave | Code.Leave_S | Code.Endfinally | Code.Ret -> ()
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
