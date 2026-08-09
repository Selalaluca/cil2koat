module CilFrontend.TransitionIr

open System.Collections.Generic
open Mono.Cecil
open CilFrontend.Cfg
open CilFrontend.Expressions
open CilFrontend.CilTypes
open CilFrontend.AbstractValues
open CilFrontend.GuardNormalization
open CilFrontend.Analysis
open CilFrontend.TransitionSyntax
open CilFrontend.TransitionValidation

let private collectProgramVariables (method: MethodDefinition) =
    // 参照型は長さだけを状態変数にし、追跡対象外の型は遷移系へ持ち込まない。
    let parameters =
        method.Parameters
        |> Seq.choose (fun parameter ->
            if isIntegerType parameter.ParameterType then Some(parameterName parameter)
            elif isStringType parameter.ParameterType || isListType parameter.ParameterType
                 || isGenericListType parameter.ParameterType || isArrayType parameter.ParameterType then
                Some(sizeVariableName (parameterName parameter))
            else None)

    let locals =
        method.Body.Variables
        |> Seq.choose (fun variable ->
            let name = sprintf "loc%d" variable.Index
            if isIntegerType variable.VariableType then Some name
            elif isStringType variable.VariableType || isListType variable.VariableType
                 || isGenericListType variable.VariableType || isArrayType variable.VariableType then
                Some(sizeVariableName name)
            elif isGenericListEnumeratorType variable.VariableType then Some(name + "_remaining")
            else None)

    Seq.append parameters locals |> Seq.distinct |> List.ofSeq

let private collectStackVariables (analysis: CfgAnalysis) =
    // 合流で導入された予約名の抽象値だけを、ブロック間で受け渡す追加状態変数として収集する。
    analysis.Blocks
    |> List.collect (fun block ->
        let label = labelOf block
        match analysis.ByLabel.TryGetValue label with
        | false, _ -> []
        | true, analysed ->
            analysed.EntryStack
            |> List.indexed
            |> List.choose (fun (index, expression) ->
                let expectedName = stackVariableName label index
                match expression with
                | IntValue(Var name) when name = expectedName -> Some name
                | StringValue(Var name) when name = expectedName -> Some name
                | ListValue(Var name) when name = expectedName -> Some name
                | GenericListValue(Var name) when name = expectedName -> Some name
                | ArrayValue(Var name) when name = expectedName -> Some name
                | ListEnumeratorValue(Var name) when name = expectedName -> Some name
                | _ -> None))
    |> List.distinct

let private libraryLoopVariable source = sprintf "summary_%s_remaining" source

let private collectLibraryLoopVariables (analysis: CfgAnalysis) =
    analysis.Blocks
    |> List.choose (fun block ->
        let source = labelOf block
        match analysis.ByLabel.TryGetValue source with
        | true, analysed when Option.isSome analysed.Simulation.LibraryLoop ->
            Some(libraryLoopVariable source)
        | _ -> None)

let private updatesFor (variables: string list) (commands: Command list) =
    // 同一ブロックで複数回代入された変数は最後のCommandを採用し、未代入変数には恒等更新を補う。
    let latest = Dictionary<string, IntExpr>()
    for command in commands do
        match command.Value with
        | IntValue expression -> latest[command.Target] <- expression
        | BoolValue _ when List.contains command.Target variables ->
            failwithf
                "整数変数 %s へBoolean式を代入することはできません。"
                command.Target
        | BoolValue _ -> ()
        | StringValue _ | ListValue _ | GenericListValue _ | ArrayValue _ | ListEnumeratorValue _
        | UnknownElementValue | LocalAddress _ | ClosureValue _ | NullValue ->
            failwithf "内部エラー: 参照値 %s が整数更新へ残っています。" command.Target

    variables
    |> List.map (fun variable ->
        let value =
            match latest.TryGetValue variable with
            | true, expression -> expression
            | false, _ -> Var variable
        variable, value)
    |> Map.ofList

/// targetの抽象入口スタック変数へ、このCFG辺から到着する実際の値を渡す。
/// 入口が具体値のスロットは状態変数ではないため更新へ追加しない。
let private passStackToTarget
    (analysis: CfgAnalysis)
    (target: BasicBlock)
    (exitStack: StackValue list)
    (updates: Map<string, IntExpr>)
    =
    let targetLabel = labelOf target
    let targetEntryStack = analysis.ByLabel[targetLabel].EntryStack

    if List.length targetEntryStack <> List.length exitStack then
        failwithf
            "遷移 %s の入口と出口で評価スタックの高さが一致しません: %d と %d"
            targetLabel
            (List.length targetEntryStack)
            (List.length exitStack)

    (updates, List.indexed (List.zip targetEntryStack exitStack))
    ||> List.fold (fun currentUpdates (index, (entryValue, exitValue)) ->
        let expectedName = stackVariableName targetLabel index
        match entryValue with
        | IntValue(Var name) when name = expectedName ->
            match exitValue with
            | IntValue expression -> Map.add name expression currentUpdates
            | _ ->
                failwithf "遷移 %s でBoolean値を整数スタック変数へ渡せません。" targetLabel
        | StringValue(Var name) when name = expectedName ->
            match exitValue with
            | StringValue length -> Map.add name length currentUpdates
            | _ -> failwithf "遷移 %s で文字列以外を文字列スタック変数へ渡せません。" targetLabel
        | ListValue(Var name) when name = expectedName ->
            match exitValue with
            | ListValue length -> Map.add name length currentUpdates
            | _ -> failwithf "遷移 %s でリスト以外をリストスタック変数へ渡せません。" targetLabel
        | GenericListValue(Var name) when name = expectedName ->
            match exitValue with
            | GenericListValue length -> Map.add name length currentUpdates
            | _ -> failwithf "遷移 %s でList<T>以外をList<T>スタック変数へ渡せません。" targetLabel
        | ArrayValue(Var name) when name = expectedName ->
            match exitValue with
            | ArrayValue length -> Map.add name length currentUpdates
            | _ -> failwithf "遷移 %s で配列以外を配列スタック変数へ渡せません。" targetLabel
        | ListEnumeratorValue(Var name) when name = expectedName ->
            match exitValue with
            | ListEnumeratorValue remaining -> Map.add name remaining currentUpdates
            | _ -> failwithf "遷移 %s でEnumerator以外をEnumeratorスタック変数へ渡せません。" targetLabel
        | _ -> currentUpdates)

let private addTransition
    (transitions: ResizeArray<Transition>)
    (source: string)
    (target: BasicBlock)
    (updates: Map<string, IntExpr>)
    (guard: BoolExpr option)
    =
    transitions.Add {
        Source = source
        Target = labelOf target
        Updates = updates
        Guard = Option.map normalize guard
    }

/// 共通CFG解析結果を、出力形式に依存しない遷移系へ変換する。
let create (method: MethodDefinition) (analysis: CfgAnalysis) : TransitionSystem =
    let programVariables = collectProgramVariables method
    let stackVariables = collectStackVariables analysis
    let libraryLoopVariables = collectLibraryLoopVariables analysis
    let generatedVariables = stackVariables @ libraryLoopVariables
    let collisions = Set.intersect (Set.ofList programVariables) (Set.ofList generatedVariables)

    if not collisions.IsEmpty then
        failwithf
            "プログラム変数名が予約済みのスタック変数名と衝突しています: %s"
            (String.concat ", " collisions)

    let variables = programVariables @ generatedVariables
    let transitions = ResizeArray<Transition>()

    for block in analysis.Blocks do
        let source = labelOf block
        match analysis.ByLabel.TryGetValue source with
        | false, _ -> ()
        | true, analysed ->
            let baseUpdates = updatesFor variables analysed.Simulation.Commands
            let updatesTo target =
                passStackToTarget analysis target analysed.Simulation.ExitStack baseUpdates

            let tailCallFallsIntoReturn =
                match analysed.Terminator with
                | MethodReturn -> true
                | FallsThrough target ->
                    target.Instructions
                    |> List.forall (fun instruction ->
                        instruction.OpCode.Code = Mono.Cecil.Cil.Code.Nop
                        || instruction.OpCode.Code = Mono.Cecil.Cil.Code.Ret)
                | _ -> false

            // 末尾再帰とライブラリ要約は通常のCFG終端より優先し、専用の遷移へ展開する。
            if analysed.Simulation.TailRecursiveCall then
                if not tailCallFallsIntoReturn then
                    failwithf "ブロック %s の再帰呼び出しは末尾位置ではありません。" source
                let entryBlock = List.head analysis.Blocks
                addTransition transitions source entryBlock baseUpdates None
            elif Option.isSome analysed.Simulation.LibraryLoop then
                if analysed.Terminator <> MethodReturn then
                    failwithf "ブロック %s のライブラリループはメソッド末尾にありません。" source

                let summary = Option.get analysed.Simulation.LibraryLoop
                let remaining = libraryLoopVariable source
                let loopLocation = source + "_library_loop"
                let entryUpdates = Map.add remaining summary.InputLength baseUpdates
                transitions.Add {
                    Source = source
                    Target = loopLocation
                    Updates = entryUpdates
                    Guard = None
                }

                // callback本体は有限性を前段で確認済み。KoATにはリスト残数が1ずつ減る走査だけを残す。
                let loopUpdates =
                    variables
                    |> List.map (fun variable ->
                        if variable = remaining then
                            variable, BinOp("-", Var remaining, Const 1)
                        else variable, Var variable)
                    |> Map.ofList
                transitions.Add {
                    Source = loopLocation
                    Target = loopLocation
                    Updates = loopUpdates
                    Guard = Some(Compare(">", Var remaining, Const 0))
                }
            else
                // 基本ブロックの終端種別を判定し、対応するKoAT向け遷移規則へ展開する。
                match analysed.Terminator with
                | MethodReturn -> ()
                | Unconditional target
                | FallsThrough target ->
                    addTransition transitions source target (updatesTo target) None
                | Conditional (trueBlock, falseBlock) ->
                    match analysed.Simulation.Guard with
                    | None -> failwithf "条件分岐 %s のガードを復元できませんでした。" source
                    | Some guard ->
                        // Cfgが真・偽の順へ正規化済みなので、偽辺には復元ガードの否定を付ける。
                        addTransition transitions source trueBlock (updatesTo trueBlock) (Some guard)
                        addTransition transitions source falseBlock (updatesTo falseBlock) (Some(BoolNot guard))
                | Switch (targets, defaultBlock) ->
                    match analysed.Simulation.SwitchValue with
                    | None -> failwithf "switch %s の値を復元できませんでした。" source
                    | Some value ->
                        for index, target in List.indexed targets do
                            addTransition
                                transitions
                                source
                                target
                                (updatesTo target)
                                (Some(Compare("==", value, Const index)))

                        // switchのdefaultは列挙した0..n-1のcase範囲外を表す。
                        let defaultGuard =
                            if targets.IsEmpty then None
                            else
                                Some(
                                    BoolOr(
                                        Compare("<", value, Const 0),
                                        Compare(">=", value, Const targets.Length)))
                        addTransition
                            transitions
                            source
                            defaultBlock
                            (updatesTo defaultBlock)
                            defaultGuard

    {
        Start = labelOf (List.head analysis.Blocks)
        Variables = variables
        Transitions = List.ofSeq transitions
    }
    |> validate
