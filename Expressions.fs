module CilFrontend.Expressions

/// KoATの整数更新として扱う算術式。
type IntExpr =
    | Const of int
    | Var of string
    | BinOp of string * IntExpr * IntExpr

/// 遷移のガードとしてだけ扱う論理式。
type BoolExpr =
    | Compare of string * IntExpr * IntExpr
    | NonZero of IntExpr
    | BoolNot of BoolExpr
    | BoolOr of BoolExpr * BoolExpr

let rec renderIntExpr = function
    | Const value -> string value
    | Var name -> name
    | BinOp (operator, left, right) ->
        sprintf "(%s %s %s)" (renderIntExpr left) operator (renderIntExpr right)

let rec renderBoolExpr = function
    | Compare (operator, left, right) ->
        sprintf "(%s %s %s)" (renderIntExpr left) operator (renderIntExpr right)
    | NonZero value -> sprintf "(%s != 0)" (renderIntExpr value)
    | BoolNot inner -> sprintf "!(%s)" (renderBoolExpr inner)
    | BoolOr (left, right) ->
        sprintf "(%s || %s)" (renderBoolExpr left) (renderBoolExpr right)
