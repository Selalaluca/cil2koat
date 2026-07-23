module CilFrontend.Koat

open System
open System.Collections.Generic
open System.IO
open Mono.Cecil
open CilFrontend.Cfg
open CilFrontend.StackSim

type private AnalysedBlock = {
    Block: BasicBlock
    Terminator: Terminator
    Simulation: SimulationResult
}

let private successors terminator =
    match terminator with
    | Unconditional target -> [ target ]
    | Conditional (trueBlock, falseBlock) -> [ trueBlock; falseBlock ]
    | Switch (targets, defaultBlock) -> defaultBlock :: targets
    | FallsThrough next -> [ next ]
    | MethodReturn -> []

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

let private analyseCfg (method: MethodDefinition) blocks =
    let entryStacks = Dictionary<string, Expr list>()
    let results = Dictionary<string, AnalysedBlock>()
    let worklist = Queue<BasicBlock>()

    let firstBlock = List.head blocks
    entryStacks.[labelOf firstBlock] <- []
    worklist.Enqueue firstBlock

    while worklist.Count > 0 do
        let block = worklist.Dequeue()
        let blockLabel = labelOf block
        let simulation =
            simulateBlock method entryStacks.[blockLabel] block.Instructions
        let terminator = classifyTerminator block blocks

        results.[blockLabel] <- {
            Block = block
            Terminator = terminator
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

    results

let private isKoatIntegerType (t: TypeReference) =
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
        |> Seq.filter (fun parameter -> isKoatIntegerType parameter.ParameterType)
        |> Seq.map parameterName

    let locals =
        method.Body.Variables
        |> Seq.filter (fun variable -> isKoatIntegerType variable.VariableType)
        |> Seq.map (fun variable -> sprintf "loc%d" variable.Index)

    Seq.append parameters locals |> Seq.distinct |> List.ofSeq

let rec private renderArithmetic expression =
    match expression with
    | Const n -> string n
    | Var name -> name
    | BinOp (("+" | "-" | "*") as op, left, right) ->
        sprintf "(%s %s %s)" (renderArithmetic left) op (renderArithmetic right)
    | BinOp (op, _, _) ->
        failwithf "KoATの多項式更新として出力できない演算です: %s" op
    | Not _ ->
        failwith "Boolean式をKoATの算術更新として出力することはできません。"

let private renderComparison op left right =
    let koatOperator =
        match op with
        | "==" -> "="
        | ">" | ">=" | "<" | "<=" -> op
        | ">u" | ">=u" | "<u" | "<=u" ->
            failwithf "符号なし比較 %s は数学的整数上でそのまま表現できません。" op
        | _ -> failwithf "未対応のガード演算です: %s" op

    sprintf "%s %s %s" (renderArithmetic left) koatOperator (renderArithmetic right)

/// KoATには論理和がないため、!= は < と > の2本の遷移へ展開する。
let rec private expandGuard expression =
    match expression with
    | BinOp ("!=", left, right) ->
        [ renderComparison "<" left right; renderComparison ">" left right ]
    | BinOp (("==" | ">" | ">=" | "<" | "<=" | ">u" | ">=u" | "<u" | "<=u") as op, left, right) ->
        [ renderComparison op left right ]
    | Var name ->
        [ sprintf "%s < 0" name; sprintf "%s > 0" name ]
    | Const 0 -> []
    | Const _ -> [ "" ]
    | Not inner ->
        match inner with
        | BinOp (">", left, right) -> [ renderComparison "<=" left right ]
        | BinOp (">=", left, right) -> [ renderComparison "<" left right ]
        | BinOp ("<", left, right) -> [ renderComparison ">=" left right ]
        | BinOp ("<=", left, right) -> [ renderComparison ">" left right ]
        | BinOp ("==", left, right) ->
            [ renderComparison "<" left right; renderComparison ">" left right ]
        | BinOp ("!=", left, right) -> [ renderComparison "==" left right ]
        | Var name -> [ sprintf "%s = 0" name ]
        | Const 0 -> [ "" ]
        | Const _ -> []
        | _ -> failwith "複合した否定ガードはまだKoAT形式へ変換できません。"
    | _ ->
        failwithf "KoAT形式へ変換できないガードです: %s" (renderExpr expression)

let private updatesFor variables commands =
    let latest = Dictionary<string, Expr>()
    for command in commands do
        latest.[command.Target] <- command.Value

    variables
    |> List.map (fun variable ->
        match latest.TryGetValue variable with
        | true, value -> renderArithmetic value
        | false, _ -> variable)

let private locationApplication label arguments =
    sprintf "%s(%s)" label (String.concat "," arguments)

let private transitionLines source target arguments updates guards =
    let lhs = locationApplication source arguments
    let rhs = locationApplication target updates

    guards
    |> List.map (fun guard ->
        if String.IsNullOrWhiteSpace guard then
            sprintf "  %s -> %s" lhs rhs
        else
            sprintf "  %s -> %s [%s]" lhs rhs guard)

let private defaultSwitchGuards value caseCount =
    if caseCount = 0 then
        [ "" ]
    else
        let rendered = renderArithmetic value
        [ sprintf "%s < 0" rendered; sprintf "%s >= %d" rendered caseCount ]

let generate (method: MethodDefinition) (blocks: BasicBlock list) =
    if blocks.IsEmpty then
        failwith "命令を持たないメソッドはKoAT形式へ変換できません。"

    let variables = collectVariables method
    let arguments = variables
    let analysed = analyseCfg method blocks
    let rules = ResizeArray<string>()

    for block in blocks do
        let source = labelOf block
        match analysed.TryGetValue source with
        | false, _ -> ()
        | true, analysis ->
            let updates = updatesFor variables analysis.Simulation.Commands

            match analysis.Terminator with
            | MethodReturn -> ()
            | Unconditional target
            | FallsThrough target ->
                transitionLines source (labelOf target) arguments updates [ "" ]
                |> List.iter rules.Add
            | Conditional (trueBlock, falseBlock) ->
                match analysis.Simulation.Guard with
                | None ->
                    failwithf "条件分岐 %s のガードを復元できませんでした。" source
                | Some guard ->
                    transitionLines source (labelOf trueBlock) arguments updates (expandGuard guard)
                    |> List.iter rules.Add
                    transitionLines source (labelOf falseBlock) arguments updates (expandGuard (Not guard))
                    |> List.iter rules.Add
            | Switch (targets, defaultBlock) ->
                match analysis.Simulation.SwitchValue with
                | None ->
                    failwithf "switch %s の値を復元できませんでした。" source
                | Some value ->
                    for index, target in List.indexed targets do
                        let guard = renderComparison "==" value (Const index)
                        transitionLines source (labelOf target) arguments updates [ guard ]
                        |> List.iter rules.Add

                    transitionLines
                        source
                        (labelOf defaultBlock)
                        arguments
                        updates
                        (defaultSwitchGuards value targets.Length)
                    |> List.iter rules.Add

    let startLabel = labelOf (List.head blocks)
    [
        "(GOAL COMPLEXITY)"
        sprintf "(STARTTERM (FUNCTIONSYMBOLS %s))" startLabel
        sprintf "(VAR %s)" (String.concat " " variables)
        "(RULES"
        yield! rules
        ")"
    ]
    |> String.concat Environment.NewLine

let writeMethod
    (method: MethodDefinition)
    (blocks: BasicBlock list)
    (outputPath: string) =

    let text = generate method blocks
    File.WriteAllText(outputPath, text)
