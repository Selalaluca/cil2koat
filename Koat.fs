module CilFrontend.Koat

open System
open System.IO
open Mono.Cecil
open CilFrontend.Cfg
open CilFrontend.StackSim
open CilFrontend.GuardNormalization
open CilFrontend.Analysis
open CilFrontend.TransitionIr

let rec private renderArithmetic expression =
    match expression with
    | Const n -> string n
    | Var name -> name
    | BinOp (("+" | "-" | "*") as op, left, right) ->
        sprintf "(%s %s %s)" (renderArithmetic left) op (renderArithmetic right)
    | BinOp (op, _, _) ->
        failwithf "KoATの多項式更新として出力できない演算です: %s" op

let private renderComparison op left right =
    let koatOperator =
        match op with
        | "==" -> "="
        | ">" | ">=" | "<" | "<=" -> op
        | ">u" | ">=u" | "<u" | "<=u" ->
            failwithf "符号なし比較 %s は数学的整数上でそのまま表現できません。" op
        | _ -> failwithf "未対応のガード演算です: %s" op

    sprintf "%s %s %s" (renderArithmetic left) koatOperator (renderArithmetic right)

/// KoATに論理和がないため、論理和と!=は複数規則へ展開する。
let rec private expandGuard expression =
    match normalize expression with
    | BoolOr (left, right) -> expandGuard left @ expandGuard right
    | Compare ("!=", left, right) ->
        [ renderComparison "<" left right; renderComparison ">" left right ]
    | Compare (("==" | ">" | ">=" | "<" | "<=" | ">u" | ">=u" | "<u" | "<=u") as op, left, right) ->
        [ renderComparison op left right ]
    | NonZero value ->
        [ renderComparison "<" value (Const 0); renderComparison ">" value (Const 0) ]
    | BoolNot _ ->
        failwith "論理和などを含む複合した否定ガードはまだKoAT形式へ変換できません。"
    | _ -> failwithf "KoAT形式へ変換できないガードです: %s" (renderBoolExpr expression)

let private locationApplication label arguments =
    sprintf "%s(%s)" label (String.concat "," arguments)

let private renderTransition (variables: string list) (transition: Transition) =
    let lhs = locationApplication transition.Source variables
    let updates =
        variables
        |> List.map (fun variable -> renderArithmetic transition.Updates.[variable])
    let rhs = locationApplication transition.Target updates
    let guards =
        match transition.Guard with
        | None -> [ "" ]
        | Some guard -> expandGuard guard

    guards
    |> List.map (fun guard ->
        if String.IsNullOrWhiteSpace guard then sprintf "  %s -> %s" lhs rhs
        else sprintf "  %s -> %s [%s]" lhs rhs guard)

let render (transitionSystem: TransitionSystem) =
    let transitionSystem = validate transitionSystem
    let rules =
        transitionSystem.Transitions
        |> List.collect (renderTransition transitionSystem.Variables)

    [
        "(GOAL COMPLEXITY)"
        sprintf "(STARTTERM (FUNCTIONSYMBOLS %s))" transitionSystem.Start
        sprintf "(VAR %s)" (String.concat " " transitionSystem.Variables)
        "(RULES"
        yield! rules
        ")"
    ]
    |> String.concat Environment.NewLine

let generateFromAnalysis (method: MethodDefinition) (analysis: CfgAnalysis) =
    TransitionIr.create method analysis |> render

/// 既存の呼び出し側との互換用。新規コードではanalyseCfgを一度だけ呼ぶ。
let generate (method: MethodDefinition) (blocks: BasicBlock list) =
    analyseCfg method blocks |> generateFromAnalysis method

let writeAnalysis (method: MethodDefinition) (analysis: CfgAnalysis) (outputPath: string) =
    File.WriteAllText(outputPath, generateFromAnalysis method analysis)

let writeMethod (method: MethodDefinition) (blocks: BasicBlock list) (outputPath: string) =
    File.WriteAllText(outputPath, generate method blocks)
