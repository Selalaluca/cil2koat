module CilFrontend.TransitionIr

open System
open System.Collections.Generic
open Mono.Cecil
open CilFrontend.Cfg
open CilFrontend.StackSim
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
        |> Seq.filter (fun parameter -> isIntegerType parameter.ParameterType)
        |> Seq.map parameterName

    let locals =
        method.Body.Variables
        |> Seq.filter (fun variable -> isIntegerType variable.VariableType)
        |> Seq.map (fun variable -> sprintf "loc%d" variable.Index)

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
            | BoolValue _ ->
                failwithf "遷移 %s でBoolean値を整数スタック変数へ渡せません。" targetLabel
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
        Guard = guard
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
