module CilFrontend.Program

open Mono.Cecil
open CilFrontend.Cfg
open CilFrontend.Expressions
open CilFrontend.AbstractValues
open CilFrontend.StackSim
open CilFrontend.Analysis
open CilFrontend.Koat
open CilFrontend.MethodSelection

[<EntryPoint>]
let main argv =
    if argv.Length < 2 then
        printfn "使い方: CilFrontend <アセンブリのパス> <メソッド指定> [出力.koat]"
        printfn "厳密指定例: static:Namespace.Type::Method(System.Int32)"
        1
    else
        let assemblyPath = argv[0]
        let methodName = argv[1]

        let assembly = AssemblyDefinition.ReadAssembly(assemblyPath)

        let methodResult =
            try Ok(selectMethod assembly methodName)
            with error -> Error error.Message

        match methodResult with
        | Error message ->
            printfn "%s" message
            1
        | Ok method when not method.HasBody ->
            printfn "メソッド '%s' は本体(IL)を持っていません。" methodName
            1
        | Ok method ->
            printfn "=== %s ===" method.FullName
            printfn ""

            printfn "--- 生のIL命令列 ---"
            for instr in method.Body.Instructions do
                printfn "%s" (formatInstruction instr)
            printfn ""

            let blocks = splitIntoBasicBlocks method.Body.Instructions
            let analysis = analyseCfg method blocks

            printfn "--- 基本ブロック分割結果 ---"
            for block in blocks do
                let blockLabel = labelOf block
                printfn "[%s]" blockLabel
                for instr in block.Instructions do
                    printfn "    %s" (formatInstruction instr)

                let terminator = classifyTerminator block blocks
                printfn "    -> 分岐先: %s" (describeTerminator terminator)

                match analysis.ByLabel.TryGetValue blockLabel with
                | false, _ ->
                    printfn "    -> 到達不能なブロック"
                | true, analysed ->
                    let simulation = analysed.Simulation
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
                            (renderBoolExpr guard)
                        printfn
                            "         %s の場合(偽): %s"
                            (labelOf falseBlock)
                            (renderBoolExpr (BoolNot guard))
                    | Switch (targets, defaultBlock), _, Some value ->
                        printfn "    -> switch条件:"
                        for index, target in List.indexed targets do
                            printfn
                                "         %s の場合: %s == %d"
                                (labelOf target)
                                (renderIntExpr value)
                                index
                        printfn "         %s の場合: default" (labelOf defaultBlock)
                    | _ -> ()

                printfn ""

            if argv.Length >= 3 then
                writeAnalysis method analysis argv[2]
                printfn "KoATファイルを書き出しました: %s" argv[2]

            0
