module CilFrontend.AbstractValues

open Mono.Cecil
open CilFrontend.Expressions

/// CILではBooleanも評価スタック上の値なので、スタック層では各抽象値を保持する。
type StackValue =
    | IntValue of IntExpr
    | BoolValue of BoolExpr
    | StringValue of length: IntExpr
    | ListValue of length: IntExpr
    | GenericListValue of length: IntExpr
    | ArrayValue of length: IntExpr
    | ListEnumeratorValue of remaining: IntExpr
    | UnknownElementValue
    | LocalAddress of name: string
    | ClosureValue of invokeMethod: MethodDefinition * captures: StackValue list
    | NullValue

type Command = { Target: string; Value: StackValue }

type LibraryLoopKind =
    | ListMapLoop
    | ListFilterLoop

/// 停止性をKoAT側で確認させる、既知ライブラリの有限走査要約。
type LibraryLoopSummary = {
    Kind: LibraryLoopKind
    InputLength: IntExpr
}

type SimulationResult = {
    Commands: Command list
    Guard: BoolExpr option
    SwitchValue: IntExpr option
    /// スタックの底から先頭の順
    ExitStack: StackValue list
    /// 同一staticメソッドへの末尾呼び出しを、戻り値の有無にかかわらず入口への遷移として扱う。
    TailRecursiveCall: bool
    LibraryLoop: LibraryLoopSummary option
}

let renderStackValue = function
    | IntValue expression -> renderIntExpr expression
    | BoolValue expression -> renderBoolExpr expression
    | StringValue length -> sprintf "string(length=%s)" (renderIntExpr length)
    | ListValue length -> sprintf "list(length=%s)" (renderIntExpr length)
    | GenericListValue length -> sprintf "List<T>(count=%s)" (renderIntExpr length)
    | ArrayValue length -> sprintf "array(length=%s)" (renderIntExpr length)
    | ListEnumeratorValue remaining -> sprintf "List<T>.Enumerator(remaining=%s)" (renderIntExpr remaining)
    | UnknownElementValue -> "foreach-element"
    | LocalAddress name -> sprintf "&%s" name
    | ClosureValue (invokeMethod, captures) ->
        sprintf "closure(%s,captures=%d)" invokeMethod.FullName captures.Length
    | NullValue -> "null"

let renderCommand command =
    sprintf "%s = %s" command.Target (renderStackValue command.Value)
