module CilFrontend.GuardNormalization

open CilFrontend.Expressions

/// 整数意味論だけで同値と分かる、局所的なガード正規化。
/// 到達可能性の推論や遷移の削除は行わない。
let rec normalize expression =
    // ガードの形を判定し、局所的に同値な簡約と否定比較の反転を再帰的に適用する。
    match expression with
    | Compare _ -> expression
    | NonZero value -> NonZero value
    | BoolOr (left, right) ->
        let normalizedLeft = normalize left
        let normalizedRight = normalize right
        if normalizedLeft = normalizedRight then normalizedLeft
        else BoolOr(normalizedLeft, normalizedRight)

    | BoolNot inner ->
        match normalize inner with
        | BoolNot nested -> normalize nested
        | Compare (">", left, right) -> Compare("<=", left, right)
        | Compare (">=", left, right) -> Compare("<", left, right)
        | Compare ("<", left, right) -> Compare(">=", left, right)
        | Compare ("<=", left, right) -> Compare(">", left, right)
        | Compare ("==", left, right) -> Compare("!=", left, right)
        | Compare ("!=", left, right) -> Compare("==", left, right)
        | NonZero value -> Compare("==", value, Const 0)
        | normalizedInner ->
            // BoolOrの否定など、現在のBoolExprでは同値な積を表せない形は残す。
            BoolNot normalizedInner
