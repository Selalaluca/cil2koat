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
    Updates: Map<string, Expr>
    Guard: Expr option
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

let private collectVariables (method: MethodDefinition) =
    let parameters =
        method.Parameters
        |> Seq.filter (fun parameter -> isIntegerType parameter.ParameterType)
        |> Seq.map parameterName

    let locals =
        method.Body.Variables
        |> Seq.filter (fun variable -> isIntegerType variable.VariableType)
        |> Seq.map (fun variable -> sprintf "loc%d" variable.Index)

    Seq.append parameters locals |> Seq.distinct |> List.ofSeq

let private updatesFor (variables: string list) (commands: Command list) =
    let latest = Dictionary<string, Expr>()
    for command in commands do
        latest.[command.Target] <- command.Value

    variables
    |> List.map (fun variable ->
        let value =
            match latest.TryGetValue variable with
            | true, expression -> expression
            | false, _ -> Var variable
        variable, value)
    |> Map.ofList

let private addTransition
    (transitions: ResizeArray<Transition>)
    (source: string)
    (target: BasicBlock)
    (updates: Map<string, Expr>)
    (guard: Expr option)
    =
    transitions.Add {
        Source = source
        Target = labelOf target
        Updates = updates
        Guard = guard
    }

/// 共通CFG解析結果を、出力形式に依存しない遷移系へ変換する。
let create (method: MethodDefinition) (analysis: CfgAnalysis) : TransitionSystem =
    let variables = collectVariables method
    let transitions = ResizeArray<Transition>()

    for block in analysis.Blocks do
        let source = labelOf block
        match analysis.ByLabel.TryGetValue source with
        | false, _ -> ()
        | true, analysed ->
            let updates = updatesFor variables analysed.Simulation.Commands
            match analysed.Terminator with
            | MethodReturn -> ()
            | Unconditional target
            | FallsThrough target ->
                addTransition transitions source target updates None
            | Conditional (trueBlock, falseBlock) ->
                match analysed.Simulation.Guard with
                | None -> failwithf "条件分岐 %s のガードを復元できませんでした。" source
                | Some guard ->
                    addTransition transitions source trueBlock updates (Some guard)
                    addTransition transitions source falseBlock updates (Some(Not guard))
            | Switch (targets, defaultBlock) ->
                match analysed.Simulation.SwitchValue with
                | None -> failwithf "switch %s の値を復元できませんでした。" source
                | Some value ->
                    for index, target in List.indexed targets do
                        addTransition transitions source target updates (Some(BinOp("==", value, Const index)))

                    let defaultGuard =
                        if targets.IsEmpty then None
                        else
                            Some(
                                BinOp(
                                    "||",
                                    BinOp("<", value, Const 0),
                                    BinOp(">=", value, Const targets.Length)))
                    addTransition transitions source defaultBlock updates defaultGuard

    {
        Start = labelOf (List.head analysis.Blocks)
        Variables = variables
        Transitions = List.ofSeq transitions
    }
