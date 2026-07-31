module CilFrontend.Analysis

open System.Collections.Generic
open Mono.Cecil
open CilFrontend.Cfg
open CilFrontend.StackSim

/// CFG解析後の、到達可能な基本ブロック1個分の情報。
type AnalysedBlock = {
    Block: BasicBlock
    Terminator: Terminator
    EntryStack: StackValue list
    Simulation: SimulationResult
}

type CfgAnalysis = {
    Blocks: BasicBlock list
    ByLabel: IReadOnlyDictionary<string, AnalysedBlock>
}

let private successors terminator =
    match terminator with
    | Unconditional target -> [ target ]
    | Conditional (trueBlock, falseBlock) -> [ trueBlock; falseBlock ]
    | Switch (targets, defaultBlock) -> defaultBlock :: targets
    | FallsThrough next -> [ next ]
    | MethodReturn -> []

/// ブロック入口の評価スタックスロットに割り当てる、予約済みの変数名。
let stackVariableName targetLabel index =
    sprintf "stack_%s_%d" targetLabel index

/// 合流元ごとに異なる式が来るスタックスロットを、ブロック入口の抽象変数にする。
let private mergeStacks targetLabel oldStack newStack =
    if List.length oldStack <> List.length newStack then
        failwithf
            "ブロック %s の入口で評価スタックの高さが一致しません: %d と %d"
            targetLabel
            (List.length oldStack)
            (List.length newStack)

    List.map3
        (fun index oldValue newValue ->
            if oldValue = newValue then oldValue
            else
                match oldValue, newValue with
                | IntValue _, IntValue _ ->
                    IntValue(Var(stackVariableName targetLabel index))
                | StringValue _, StringValue _ ->
                    StringValue(Var(stackVariableName targetLabel index))
                | ListValue _, ListValue _ ->
                    ListValue(Var(stackVariableName targetLabel index))
                | GenericListValue _, GenericListValue _ ->
                    GenericListValue(Var(stackVariableName targetLabel index))
                | ArrayValue _, ArrayValue _ ->
                    ArrayValue(Var(stackVariableName targetLabel index))
                | ListEnumeratorValue _, ListEnumeratorValue _ ->
                    ListEnumeratorValue(Var(stackVariableName targetLabel index))
                | UnknownElementValue, UnknownElementValue -> UnknownElementValue
                | NullValue, NullValue -> NullValue
                | BoolValue _, BoolValue _ ->
                    failwithf
                        "ブロック %s の入口で異なるBooleanスタック値を合流できません。"
                        targetLabel
                | _ ->
                    failwithf
                        "ブロック %s の入口で異なる種類のスタック値を合流できません。"
                        targetLabel)
        [ 0 .. List.length oldStack - 1 ]
        oldStack
        newStack

/// CFG上で入口スタックを伝播し、到達可能な各ブロックを一度だけ共通解析する。
let analyseCfg (method: MethodDefinition) (blocks: BasicBlock list) =
    if blocks.IsEmpty then
        failwith "命令を持たないメソッドは解析できません。"

    let entryStacks = Dictionary<string, StackValue list>()
    let results = Dictionary<string, AnalysedBlock>()
    let worklist = Queue<BasicBlock>()
    let firstBlock = List.head blocks

    entryStacks.[labelOf firstBlock] <- []
    worklist.Enqueue firstBlock

    while worklist.Count > 0 do
        let block = worklist.Dequeue()
        let blockLabel = labelOf block
        let entryStack = entryStacks.[blockLabel]
        let simulation = simulateBlock method entryStack block.Instructions
        let terminator = classifyTerminator block blocks

        results.[blockLabel] <- {
            Block = block
            Terminator = terminator
            EntryStack = entryStack
            Simulation = simulation
        }

        for target in successors terminator do
            let targetLabel = labelOf target
            match entryStacks.TryGetValue targetLabel with
            | false, _ ->
                entryStacks.[targetLabel] <- simulation.ExitStack
                worklist.Enqueue target
            | true, oldStack ->
                let merged = mergeStacks targetLabel oldStack simulation.ExitStack
                if merged <> oldStack then
                    entryStacks.[targetLabel] <- merged
                    worklist.Enqueue target

    {
        Blocks = blocks
        ByLabel = results
    }
