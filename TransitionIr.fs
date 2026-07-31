module CilFrontend.TransitionIr

open System
open System.Collections.Generic
open Mono.Cecil
open CilFrontend.Cfg
open CilFrontend.StackSim
open CilFrontend.GuardNormalization
open CilFrontend.Analysis

/// 1本の制御フロー辺。更新とガードはまだ文字列化しない。
type Transition = {
    Source: string
    Target: string
    Updates: Map<string, IntExpr>
    Guard: BoolExpr option
}

type TransitionSystem = {
    Start: string
    Variables: string list
    Transitions: Transition list
}

/// バックエンドが前提とする遷移IRの構造的不変条件を検査する。
let validate (transitionSystem: TransitionSystem) =
    if String.IsNullOrWhiteSpace transitionSystem.Start then
        failwith "遷移系の開始位置が空です。"

    let duplicateVariables =
        transitionSystem.Variables
        |> List.countBy id
        |> List.choose (fun (name, count) -> if count > 1 then Some name else None)

    if not duplicateVariables.IsEmpty then
        failwithf
            "遷移系に重複した変数があります: %s"
            (String.concat ", " duplicateVariables)

    let expectedVariables = Set.ofList transitionSystem.Variables
    for transition in transitionSystem.Transitions do
        if String.IsNullOrWhiteSpace transition.Source
           || String.IsNullOrWhiteSpace transition.Target then
            failwith "遷移の制御位置が空です。"

        let actualVariables =
            transition.Updates |> Map.toSeq |> Seq.map fst |> Set.ofSeq
        if actualVariables <> expectedVariables then
            let missing = Set.difference expectedVariables actualVariables
            let unknown = Set.difference actualVariables expectedVariables
            failwithf
                "遷移 %s -> %s の更新集合が不正です。不足: [%s] 未宣言: [%s]"
                transition.Source
                transition.Target
                (String.concat ", " missing)
                (String.concat ", " unknown)

    transitionSystem

let private isIntegerType (t: TypeReference) =
    match t.MetadataType with
    | MetadataType.SByte
    | MetadataType.Byte
    | MetadataType.Int16
    | MetadataType.UInt16
    | MetadataType.Int32
    | MetadataType.UInt32
    | MetadataType.Int64
    | MetadataType.UInt64 -> true
    | _ -> false

let private parameterName (parameter: ParameterDefinition) =
    if String.IsNullOrWhiteSpace parameter.Name then
        sprintf "arg%d" parameter.Index
    else
        parameter.Name

let private collectProgramVariables (method: MethodDefinition) =
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

let private updatesFor (variables: string list) (commands: Command list) =
    let latest = Dictionary<string, IntExpr>()
    for command in commands do
        match command.Value with
        | IntValue expression -> latest.[command.Target] <- expression
        | BoolValue _ when List.contains command.Target variables ->
            failwithf
                "整数変数 %s へBoolean式を代入することはできません。"
                command.Target
        | BoolValue _ -> ()
        | StringValue _ | ListValue _ | GenericListValue _ | ArrayValue _ | ListEnumeratorValue _
        | UnknownElementValue | LocalAddress _ | NullValue ->
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
let private passStackToTarget
    (analysis: CfgAnalysis)
    (target: BasicBlock)
    (exitStack: StackValue list)
    (updates: Map<string, IntExpr>)
    =
    let targetLabel = labelOf target
    let targetEntryStack = analysis.ByLabel.[targetLabel].EntryStack

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
    let collisions = Set.intersect (Set.ofList programVariables) (Set.ofList stackVariables)

    if not collisions.IsEmpty then
        failwithf
            "プログラム変数名が予約済みのスタック変数名と衝突しています: %s"
            (String.concat ", " collisions)

    let variables = programVariables @ stackVariables
    let transitions = ResizeArray<Transition>()

    for block in analysis.Blocks do
        let source = labelOf block
        match analysis.ByLabel.TryGetValue source with
        | false, _ -> ()
        | true, analysed ->
            let baseUpdates = updatesFor variables analysed.Simulation.Commands
            let updatesTo target =
                passStackToTarget analysis target analysed.Simulation.ExitStack baseUpdates

            match analysed.Terminator with
            | MethodReturn -> ()
            | Unconditional target
            | FallsThrough target ->
                addTransition transitions source target (updatesTo target) None
            | Conditional (trueBlock, falseBlock) ->
                match analysed.Simulation.Guard with
                | None -> failwithf "条件分岐 %s のガードを復元できませんでした。" source
                | Some guard ->
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
