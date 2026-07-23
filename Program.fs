module CilFrontend.Program

open System.Collections.Generic
open Mono.Cecil
open CilFrontend.Cfg
open CilFrontend.StackSim

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

/// CFG上で入口スタックを伝播し、到達可能な各ブロックをシミュレーションする。
let private simulateCfg method blocks =
    let entryStacks = Dictionary<string, Expr list>()
    let results = Dictionary<string, SimulationResult>()
    let worklist = Queue<BasicBlock>()

    let firstBlock = List.head blocks
    entryStacks.[labelOf firstBlock] <- []
    worklist.Enqueue firstBlock

    while worklist.Count > 0 do
        let block = worklist.Dequeue()
        let blockLabel = labelOf block
        let initialStack = entryStacks.[blockLabel]
        let result = simulateBlock method initialStack block.Instructions
        results.[blockLabel] <- result

        let terminator = classifyTerminator block blocks
        for target in successors terminator do
            let targetLabel = labelOf target
            match entryStacks.TryGetValue targetLabel with
            | false, _ ->
                entryStacks.[targetLabel] <- result.ExitStack
                worklist.Enqueue target
            | true, oldStack ->
                let merged = mergeStacks targetLabel oldStack result.ExitStack
                if merged <> oldStack then
                    entryStacks.[targetLabel] <- merged
                    worklist.Enqueue target

    results

[<EntryPoint>]
let main argv =
    if argv.Length < 2 then
        printfn "使い方: CilFrontend <アセンブリのパス> <メソッド名>"
        1
    else
        let assemblyPath = argv.[0]
        let methodName = argv.[1]

        let assembly = AssemblyDefinition.ReadAssembly(assemblyPath)

        let methodOpt =
            assembly.MainModule.Types
            |> Seq.collect (fun t -> t.Methods)
            |> Seq.tryFind (fun m -> m.Name = methodName)

        match methodOpt with
        | None ->
            printfn "メソッド '%s' が見つかりませんでした。" methodName
            1
        | Some method when not method.HasBody ->
            printfn "メソッド '%s' は本体(IL)を持っていません。" methodName
            1
        | Some method ->
            printfn "=== %s ===" method.FullName
            printfn ""

            printfn "--- 生のIL命令列 ---"
            for instr in method.Body.Instructions do
                printfn "%s" (formatInstruction instr)
            printfn ""

            let blocks = splitIntoBasicBlocks method.Body.Instructions
            let results = simulateCfg method blocks

            printfn "--- 基本ブロック分割結果 ---"
            for block in blocks do
                let blockLabel = labelOf block
                printfn "[%s]" blockLabel
                for instr in block.Instructions do
                    printfn "    %s" (formatInstruction instr)

                let terminator = classifyTerminator block blocks
                printfn "    -> 分岐先: %s" (describeTerminator terminator)

                match results.TryGetValue blockLabel with
                | false, _ ->
                    printfn "    -> 到達不能なブロック"
                | true, simulation ->
                    if not simulation.Commands.IsEmpty then
                        printfn "    -> 変数化した代入文:"
                        for cmd in simulation.Commands do
                            printfn "         %s" (renderCommand cmd)

                    match terminator, simulation.Guard, simulation.SwitchValue with
                    | Conditional (trueBlock, falseBlock), Some guard, _ ->
                        printfn "    -> ガード条件:"
                        printfn
                            "         %s の場合(真): %s"
                            (labelOf trueBlock)
                            (renderExpr guard)
                        printfn
                            "         %s の場合(偽): %s"
                            (labelOf falseBlock)
                            (renderExpr (Not guard))
                    | Switch (targets, defaultBlock), _, Some value ->
                        printfn "    -> switch条件:"
                        for index, target in List.indexed targets do
                            printfn
                                "         %s の場合: %s == %d"
                                (labelOf target)
                                (renderExpr value)
                                index
                        printfn "         %s の場合: default" (labelOf defaultBlock)
                    | _ -> ()

                printfn ""

            0
