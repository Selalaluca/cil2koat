module CilFrontend.StackSim

open System
open System.Collections.Generic
open Mono.Cecil
open Mono.Cecil.Cil
open CilFrontend.Expressions
open CilFrontend.CilTypes
open CilFrontend.AbstractValues

let simulateBlock
    (method: MethodDefinition)
    (initialStack: StackValue list)
    (instructions: Instruction list)
    : SimulationResult =

    // CFG辺から渡されたスタックは底から先頭の順なので、その順にPushしてCILのスタックを復元する。
    let stack = Stack<StackValue>()
    for value in initialStack do stack.Push value

    let commands = ResizeArray<Command>()
    let environment = Dictionary<string, StackValue>()
    let mutable guard = None
    let mutable switchValue = None
    let mutable currentInstruction: Instruction option = None
    let mutable tailRecursiveCall = false
    let mutable libraryLoop = None

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
        | UnknownElementValue | LocalAddress _ | ClosureValue _ | NullValue ->
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
        | GenericListValue _ | ArrayValue _ | ListEnumeratorValue _ | UnknownElementValue | LocalAddress _
        | ClosureValue _ ->
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
        // 参照型は値そのものではなく長さ・残数へ抽象化する。
        // environmentは同一ブロック内の後続命令用、CommandはCFG辺の更新生成用で、両方の更新が必要になる。
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
                | ClosureValue _ ->
                    failwithf "%s で関数値を整数変数 %s へ代入することはできません。" (instructionText ()) name
                | _ -> value, Some { Target = name; Value = value }

        environment[name] <- storedValue
        command |> Option.iter commands.Add

    let argumentType index =
        if method.HasThis then
            if index = 0 then method.DeclaringType :> TypeReference
            else method.Parameters[index - 1].ParameterType
        else
            method.Parameters[index].ParameterType

    let localAt index = method.Body.Variables[index]

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
        // C#コンパイラがx != 0をcgt.un x 0へ落とす既知形だけ、数学的整数上の!=へ安全に戻す。
        match right with
        | Const 0 -> Compare("!=", left, right)
        | _ -> Compare(">u", left, right)

    let popCallArguments count =
        // CILは左から評価した引数を順に積むため、popした並びを反転して宣言順へ戻す。
        [ for index in 1 .. count -> pop (sprintf "呼び出し引数 %d" index) ]
        |> List.rev

    let isIntegerLikeType (t: TypeReference) =
        match t.MetadataType with
        | MetadataType.SByte | MetadataType.Byte
        | MetadataType.Int16 | MetadataType.UInt16
        | MetadataType.Int32 | MetadataType.UInt32
        | MetadataType.Int64 | MetadataType.UInt64 -> true
        | _ -> false

    let validateSimpleCallback (invokeMethod: MethodDefinition) =
        // map/filterの1反復を有限とみなす根拠をここで確認する。
        // 未知call、状態更新、後方分岐を許可リストから外し、判断できないcallbackは変換しない。
        if not invokeMethod.HasBody then
            failwithf "callback %s はCIL本体を持っていません。" invokeMethod.FullName

        let instructions = List.ofSeq invokeMethod.Body.Instructions
        let offsets = instructions |> List.map (fun instruction -> instruction.Offset) |> Set.ofList

        let branchTargets (instruction: Instruction) =
            match instruction.Operand with
            | :? Instruction as target -> [ target ]
            | :? (Instruction array) as targets -> List.ofArray targets
            | _ -> []

        for instruction in instructions do
            let supported =
                match instruction.OpCode.Code with
                | Code.Nop | Code.Ret
                | Code.Ldarg_0 | Code.Ldarg_1 | Code.Ldarg_2 | Code.Ldarg_3
                | Code.Ldarg | Code.Ldarg_S
                | Code.Ldc_I4_M1 | Code.Ldc_I4_0 | Code.Ldc_I4_1 | Code.Ldc_I4_2
                | Code.Ldc_I4_3 | Code.Ldc_I4_4 | Code.Ldc_I4_5 | Code.Ldc_I4_6
                | Code.Ldc_I4_7 | Code.Ldc_I4_8 | Code.Ldc_I4 | Code.Ldc_I4_S
                | Code.Ldfld
                | Code.Add | Code.Sub | Code.Mul | Code.Neg | Code.Conv_I4
                | Code.Ceq | Code.Cgt | Code.Clt
                | Code.Br | Code.Br_S
                | Code.Brtrue | Code.Brtrue_S | Code.Brfalse | Code.Brfalse_S
                | Code.Beq | Code.Beq_S | Code.Bne_Un | Code.Bne_Un_S
                | Code.Bgt | Code.Bgt_S | Code.Bge | Code.Bge_S
                | Code.Blt | Code.Blt_S | Code.Ble | Code.Ble_S -> true
                | _ -> false

            if not supported then
                failwithf
                    "callback %s は未対応命令 IL_%04X (%s) を含みます。"
                    invokeMethod.FullName instruction.Offset instruction.OpCode.Name

            match instruction.OpCode.Code, instruction.Operand with
            | Code.Ldfld, (:? FieldReference as field) when not (isIntegerLikeType field.FieldType) ->
                failwithf "callback %s は整数以外のフィールド %s を読み取ります。" invokeMethod.FullName field.FullName
            | Code.Ldfld, _ -> ()
            | _ -> ()

            for target in branchTargets instruction do
                if not (Set.contains target.Offset offsets) then
                    failwithf "callback %s の分岐先がメソッド本体の外です。" invokeMethod.FullName
                if target.Offset <= instruction.Offset then
                    failwithf "callback %s は循環する可能性があるため未対応です。" invokeMethod.FullName

    let pushClosure (closureType: TypeDefinition) captures =
        // 閉じた世界でInvoke本体を1つに解決できるクロージャだけを抽象値として保持する。
        let invokeMethods =
            closureType.Methods
            |> Seq.filter (fun candidate -> candidate.Name = "Invoke" && candidate.HasBody)
            |> Seq.toList
        match invokeMethods with
        | [ invokeMethod ] ->
            validateSimpleCallback invokeMethod
            stack.Push(ClosureValue(invokeMethod, captures))
        | [] -> failwithf "クロージャ型 %s にInvoke本体がありません。" closureType.FullName
        | _ -> failwithf "クロージャ型 %s のInvokeを一意に特定できません。" closureType.FullName

    let createClosure (constructor: MethodReference) =
        let captures = popCallArguments constructor.Parameters.Count
        for parameter, capture in Seq.zip constructor.Parameters captures do
            if not (isIntegerLikeType parameter.ParameterType) then
                failwithf "クロージャ %s の整数以外のキャプチャ %s は未対応です。" constructor.DeclaringType.FullName parameter.ParameterType.FullName
            match capture with
            | IntValue _ -> ()
            | _ -> failwithf "クロージャ %s のキャプチャ値は整数式ではありません。" constructor.DeclaringType.FullName

        pushClosure (constructor.DeclaringType.Resolve()) captures

    let loadStaticClosure (field: FieldReference) =
        let closureType = field.FieldType.Resolve()
        if isNull closureType then
            failwithf "%s の静的フィールド型を解決できません。" (instructionText ())
        pushClosure closureType []

    let handleNewObject (constructor: MethodReference) =
        let arguments = popCallArguments constructor.Parameters.Count
        let declaringType = constructor.DeclaringType.FullName

        if declaringType.StartsWith(
            "Microsoft.FSharp.Collections.FSharpList`1",
            StringComparison.Ordinal) then
            match arguments with
            | [ _; ListValue tailLength ] ->
                // FSharpListのconsセル。要素値は停止性IRでは追跡せず、長さだけを増やす。
                stack.Push(ListValue(BinOp("+", tailLength, Const 1)))
            | _ ->
                failwithf "%s のFSharpListコンストラクター引数が不正です。" (instructionText ())
        elif declaringType.StartsWith("System.Tuple`", StringComparison.Ordinal)
             || declaringType.StartsWith("System.ValueTuple`", StringComparison.Ordinal) then
            // タプルの内容はリスト長抽象化に影響しない。不透明な要素値として保持する。
            stack.Push UnknownElementValue
        else
            // その他のnewobjは、既存のキャプチャ付きクロージャ生成として検査する。
            // createClosure内でも引数をpopするため、ここで取り出した値を積み直す。
            arguments |> List.iter stack.Push
            createClosure constructor

    let handleCall (called: MethodReference) =
        // call命令は末尾再帰と既知ライブラリ要約にだけ展開する。
        // 一般のcallを副作用なしと仮定すると停止性を誤証明し得るため、未知呼び出しは明示的に拒否する。
        let arguments = popCallArguments called.Parameters.Count
        let receiver =
            if called.HasThis then Some(pop "インスタンスメソッドのレシーバー")
            else None

        let isSelfCall = called.FullName = method.FullName
        // call後がnop/retだけなら、復帰後に追加計算がない末尾位置として扱える。
        let isTailPosition =
            match currentInstruction with
            | None -> false
            | Some current ->
                instructions
                |> List.skipWhile (fun instruction -> instruction.Offset <> current.Offset)
                |> List.skip 1
                |> List.forall (fun instruction ->
                    instruction.OpCode.Code = Code.Nop || instruction.OpCode.Code = Code.Ret)

        let setLibraryLoop kind length =
            // 現在のIRは基本ブロック途中へ継続位置を挿入できないため、map/filterが末尾にある場合だけ展開する。
            if not isTailPosition then
                failwithf
                    "%s のList.map／List.filter結果を後続処理で使う明示ループ変換は未対応です。"
                    (instructionText ())
            if Option.isSome libraryLoop then
                failwithf "%s の基本ブロックには複数のライブラリループがあります。" (instructionText ())
            libraryLoop <- Some { Kind = kind; InputLength = length }

        if isSelfCall then
            if method.HasThis then
                failwithf "%s のinstance再帰は未対応です。" (instructionText ())
            if not isTailPosition then
                failwithf "%s の非末尾再帰は呼び出しスタックが必要なため未対応です。" (instructionText ())
            if arguments.Length <> method.Parameters.Count then
                failwithf "%s の再帰呼び出し引数数が一致しません。" (instructionText ())

            List.zip (List.ofSeq method.Parameters) arguments
            |> List.iter (fun (parameter, value) ->
                writeVariable (parameterName parameter) parameter.ParameterType value)
            tailRecursiveCall <- true
        else
            // 呼出し先の型・名前、receiver、引数の抽象値から、対応済みライブラリ操作の効果を判定する。
            match called.DeclaringType.FullName, called.Name, receiver, arguments with
            | "System.String", "get_Length", Some(StringValue length), [] ->
                stack.Push(IntValue length)
            | "System.String", "IsNullOrEmpty", None, [ StringValue length ] ->
                stack.Push(BoolValue(Compare("==", length, Const 0)))
            | "System.String", "IsNullOrEmpty", None, [ NullValue ] ->
                stack.Push(BoolValue(Compare("==", Const 0, Const 0)))

            | declaringType, "get_Empty", None, []
                when declaringType.StartsWith(
                    "Microsoft.FSharp.Collections.FSharpList`1",
                    StringComparison.Ordinal) ->
                stack.Push(ListValue(Const 0))
            | declaringType, "Cons", None, [ _; ListValue tailLength ]
                when declaringType.StartsWith(
                    "Microsoft.FSharp.Collections.FSharpList`1",
                    StringComparison.Ordinal) ->
                // 要素値は捨象し、consによる長さの増加だけを保持する。
                stack.Push(ListValue(BinOp("+", tailLength, Const 1)))

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
            | "Microsoft.FSharp.Collections.ListModule", ("Reverse" | "Rev"), None, [ ListValue length ] ->
                // 反転は有限リストを一度走査するが、結果の長さは変わらない。
                stack.Push(ListValue length)

            | "Microsoft.FSharp.Collections.ListModule", "Map", None,
                [ ClosureValue _; ListValue length ] ->
                // callbackの有限性はClosureValue構築時に検査済み。ここではリスト走査回数だけを要約する。
                setLibraryLoop ListMapLoop length
                stack.Push(ListValue length)
            | "Microsoft.FSharp.Collections.ListModule", "Filter", None,
                [ ClosureValue _; ListValue length ] ->
                setLibraryLoop ListFilterLoop length
                stack.Push(ListValue length)
            | "Microsoft.FSharp.Collections.ListModule", "Sort", None, [ ListValue length ] ->
                // List.sortは要素数を保存する有限ライブラリ処理として要約する。
                // 比較回数の計算量は扱わず、停止性のための有限な残数ループだけをIRへ残す。
                setLibraryLoop ListSortLoop length
                stack.Push(ListValue length)

            | declaringType, "get_Count", Some(GenericListValue length), []
                when declaringType.StartsWith("System.Collections.Generic.List`1", StringComparison.Ordinal) ->
                stack.Push(IntValue length)
            | declaringType, "GetEnumerator", Some(GenericListValue length), []
                when declaringType.StartsWith("System.Collections.Generic.List`1", StringComparison.Ordinal) ->
                stack.Push(ListEnumeratorValue length)
            | declaringType, "MoveNext", Some(LocalAddress name), []
                when declaringType.StartsWith("System.Collections.Generic.List`1/Enumerator", StringComparison.Ordinal) ->
                // MoveNextの戻り値は更新前のremaining > 0、次回状態はremaining - 1として同時に表す。
                let variable = localAt (Int32.Parse(name.Substring(3)))
                match readVariable name variable.VariableType with
                | ListEnumeratorValue remaining ->
                    let next = BinOp("-", remaining, Const 1)
                    environment[name] <- ListEnumeratorValue next
                    commands.Add { Target = name + "_remaining"; Value = IntValue next }
                    stack.Push(BoolValue(Compare(">", remaining, Const 0)))
                | _ -> failwithf "%s のEnumerator状態が不正です。" (instructionText ())
            | declaringType, "get_Current", Some(LocalAddress _), []
                when declaringType.StartsWith("System.Collections.Generic.List`1/Enumerator", StringComparison.Ordinal) ->
                stack.Push UnknownElementValue
            | _, "Dispose", Some(LocalAddress _), [] -> ()

            | _ ->
                failwithf
                    "未対応の呼び出しです: %s（対応済みのstring/list/foreach操作と同一staticメソッドへの末尾再帰だけを扱えます。）"
                    called.FullName

    // 各命令は抽象スタック・環境・ガード・要約のいずれかを更新する。
    // 対応できない命令は値を推測せず、このブロックの変換全体を失敗させる。
    for instr in instructions do
        currentInstruction <- Some instr
        // opcodeを判定し、抽象スタック・変数環境・ガード・呼出し要約の対応する状態へ反映する。
        match instr.OpCode.Code with
        | Code.Nop -> ()
        | Code.Ldarg_0 -> stack.Push(readVariable (argumentName method 0) (argumentType 0))
        | Code.Ldarg_1 -> stack.Push(readVariable (argumentName method 1) (argumentType 1))
        | Code.Ldarg_2 -> stack.Push(readVariable (argumentName method 2) (argumentType 2))
        | Code.Ldarg_3 -> stack.Push(readVariable (argumentName method 3) (argumentType 3))
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
        | Code.Ldsfld -> loadStaticClosure (instr.Operand :?> FieldReference)
        | Code.Newarr ->
            let length = popInt "配列の長さ"
            stack.Push(ArrayValue length)
        | Code.Newobj ->
            handleNewObject (instr.Operand :?> MethodReference)
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
        | Code.Constrained | Code.Tail -> ()
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
        TailRecursiveCall = tailRecursiveCall
        LibraryLoop = libraryLoop
    }
