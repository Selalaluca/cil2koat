module CilFrontend.TransitionSyntax

open CilFrontend.Expressions

/// 1本の制御フロー辺。更新とガードはまだ文字列化しない。
type Transition = {
    Source: string
    Target: string
    Updates: Map<string, IntExpr>
    Guard: BoolExpr option
}

type TransitionSystem = {
    Start: string
    Variables: string list
    Transitions: Transition list
}
