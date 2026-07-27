module CilFrontend.Analysis

open System.Collections.Generic
open Mono.Cecil
open CilFrontend.Cfg
open CilFrontend.StackSim

/// CFG解析後の、到達可能な基本ブロック1個分の情報。
type AnalysedBlock = {
    Block: BasicBlock
    Terminator: Terminator
    EntryStack: Expr list
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
            else Var(sprintf "stack_%s_%d" targetLabel index))
        [ 0 .. List.length oldStack - 1 ]
        oldStack
        newStack

/// CFG上で入口スタックを伝播し、到達可能な各ブロックを一度だけ共通解析する。
let analyseCfg (method: MethodDefinition) (blocks: BasicBlock list) =
    if blocks.IsEmpty then
        failwith "命令を持たないメソッドは解析できません。"

    let entryStacks = Dictionary<string, Expr list>()
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
