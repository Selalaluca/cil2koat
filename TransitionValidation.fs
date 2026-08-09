module CilFrontend.TransitionValidation

open System
open CilFrontend.TransitionSyntax

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
