module CilFrontend.Cfg

open Mono.Cecil.Cil

/// 基本ブロック: 分岐や合流のない、連続した命令列
type BasicBlock = { Instructions: Instruction list }

/// IL命令1つを "IL_XXXX: opcode operand" の形の文字列にする
let formatInstruction (instr: Instruction) =
    let operandText =
        match instr.Operand with
        | :? Instruction as target -> sprintf "IL_%04X" target.Offset
        | null -> ""
        | other -> other.ToString()

    sprintf "IL_%04X: %-10s %s" instr.Offset instr.OpCode.Name operandText

/// 分岐命令から、CFG構築に使う「リーダー(ブロックの先頭になる命令)」のオフセット集合を求める
let private collectLeaderOffsets (instructions: Instruction seq) =
    let instructionsList = instructions |> List.ofSeq
    let leaders = System.Collections.Generic.SortedSet<int>()

    match instructionsList with
    | first :: _ -> leaders.Add(first.Offset) |> ignore
    | [] -> ()

    for instr in instructionsList do
        match instr.OpCode.FlowControl with
        | FlowControl.Branch | FlowControl.Cond_Branch ->
            match instr.Operand with
            | :? Instruction as target -> leaders.Add(target.Offset) |> ignore
            | :? (Instruction array) as targets ->
                for target in targets do
                    leaders.Add(target.Offset) |> ignore
            | _ -> ()

            let nextOffset = instr.Offset + instr.GetSize()
            instructionsList
            |> List.tryFind (fun i -> i.Offset = nextOffset)
            |> Option.iter (fun _ -> leaders.Add(nextOffset) |> ignore)
        | _ -> ()

    leaders

/// 命令列を基本ブロックのリストに分割する
let splitIntoBasicBlocks (instructions: Instruction seq) : BasicBlock list =
    let leaders = collectLeaderOffsets instructions

    let blocks = System.Collections.Generic.List<BasicBlock>()
    let current = System.Collections.Generic.List<Instruction>()

    for instr in instructions do
        if leaders.Contains(instr.Offset) && current.Count > 0 then
            blocks.Add({ Instructions = List.ofSeq current })
            current.Clear()

        current.Add(instr)

    if current.Count > 0 then
        blocks.Add({ Instructions = List.ofSeq current })

    List.ofSeq blocks

let labelOf (b: BasicBlock) = sprintf "block_%04X" (List.head b.Instructions).Offset

/// ブロックの終端を、文字列ではなく構造化データとして分類する。
/// StackSimのguardと組み合わせられるよう、Conditionalは「真の枝→偽の枝」の順で持つ。
type Terminator =
    | Unconditional of target: BasicBlock
    | Conditional of trueBlock: BasicBlock * falseBlock: BasicBlock
    | Switch of targets: BasicBlock list * defaultBlock: BasicBlock
    | MethodReturn
    | FallsThrough of next: BasicBlock

let classifyTerminator (block: BasicBlock) (allBlocks: BasicBlock list) : Terminator =
    let findBlockStartingAt offset =
        allBlocks
        |> List.find (fun b -> (List.head b.Instructions).Offset = offset)
        // 見つからない場合は例外(このプロトタイプでは異常系は未対応)

    let last = List.last block.Instructions

    match last.OpCode.Code, last.OpCode.FlowControl with
    | Code.Switch, _ ->
        let targets =
            last.Operand :?> Instruction array
            |> Array.map (fun target -> findBlockStartingAt target.Offset)
            |> List.ofArray

        let defaultOffset = last.Offset + last.GetSize()
        Switch(targets, findBlockStartingAt defaultOffset)

    | _, FlowControl.Branch ->
        let target = last.Operand :?> Instruction
        Unconditional(findBlockStartingAt target.Offset)

    | _, FlowControl.Cond_Branch ->
        // brfalse系は「偽の時に分岐先へ」なので、brtrue系とは真偽の意味が逆になる
        let branchMeansTrue =
            match last.OpCode.Code with
            | Code.Brfalse | Code.Brfalse_S -> false
            | _ -> true

        let branchTarget = last.Operand :?> Instruction
        let branchBlock = findBlockStartingAt branchTarget.Offset
        let fallThroughOffset = last.Offset + last.GetSize()
        let fallThroughBlock = findBlockStartingAt fallThroughOffset

        if branchMeansTrue then
            Conditional(branchBlock, fallThroughBlock)
        else
            Conditional(fallThroughBlock, branchBlock)

    | _, FlowControl.Return -> MethodReturn

    | _ ->
        let nextOffset = last.Offset + last.GetSize()
        FallsThrough(findBlockStartingAt nextOffset)

let describeTerminator (t: Terminator) =
    match t with
    | Unconditional target -> sprintf "%s (無条件)" (labelOf target)
    | Conditional (trueBlock, falseBlock) ->
        sprintf "%s (真) / %s (偽)" (labelOf trueBlock) (labelOf falseBlock)
    | Switch (targets, defaultBlock) ->
        let cases = targets |> List.map labelOf |> String.concat ", "
        sprintf "%s / default: %s" cases (labelOf defaultBlock)
    | MethodReturn -> "(メソッド終了)"
    | FallsThrough next -> labelOf next
