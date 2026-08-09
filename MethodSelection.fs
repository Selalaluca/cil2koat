module CilFrontend.MethodSelection

open System
open Mono.Cecil

type Dispatch =
    | Any
    | Static
    | Instance

type MethodSelector = {
    TypeName: string
    MethodName: string
    ParameterTypes: string list
    Dispatch: Dispatch
}

let private dispatchPrefix (methodDefinition: MethodDefinition) =
    if methodDefinition.HasThis then "instance:" else "static:"

let canonicalSelector (methodDefinition: MethodDefinition) =
    // static/instanceを含め、同名オーバーロードを一意に再指定できる表現を生成する。
    let parameters =
        methodDefinition.Parameters
        |> Seq.map (fun parameter -> parameter.ParameterType.FullName)
        |> String.concat ","
    sprintf
        "%s%s::%s(%s)"
        (dispatchPrefix methodDefinition)
        methodDefinition.DeclaringType.FullName
        methodDefinition.Name
        parameters

let private allMethods (assembly: AssemblyDefinition) =
    // F#クロージャなどはnested typeに生成されるため、トップレベル型だけでなく再帰的に列挙する。
    let rec methodsOfType (typeDefinition: TypeDefinition) =
        seq {
            yield! typeDefinition.Methods
            for nestedType in typeDefinition.NestedTypes do
                yield! methodsOfType nestedType
        }

    assembly.MainModule.Types |> Seq.collect methodsOfType |> Seq.toList

let private parseDispatch (text: string) =
    if text.StartsWith("static:", StringComparison.OrdinalIgnoreCase) then
        Static, text.Substring("static:".Length)
    elif text.StartsWith("instance:", StringComparison.OrdinalIgnoreCase) then
        Instance, text.Substring("instance:".Length)
    else
        Any, text

let private parseExactSelector (text: string) =
    let dispatch, body = parseDispatch text
    let separator = body.IndexOf("::", StringComparison.Ordinal)
    let openParenthesis = body.IndexOf('(', max 0 (separator + 2))
    let closeParenthesis = body.LastIndexOf(')')

    if separator <= 0
       || openParenthesis <= separator + 2
       || closeParenthesis <> body.Length - 1 then
        failwithf
            "メソッド指定の形式が不正です: %s。形式: 型::メソッド(引数型,...)"
            text

    let parameterText =
        body.Substring(openParenthesis + 1, closeParenthesis - openParenthesis - 1)

    {
        TypeName = body.Substring(0, separator)
        MethodName =
            body.Substring(separator + 2, openParenthesis - separator - 2)
        ParameterTypes =
            if String.IsNullOrWhiteSpace parameterText then []
            else
                parameterText.Split(',')
                |> Array.map (fun parameter -> parameter.Trim())
                |> Array.toList
        Dispatch = dispatch
    }

let private dispatchMatches dispatch (methodDefinition: MethodDefinition) =
    match dispatch with
    | Any -> true
    | Static -> not methodDefinition.HasThis
    | Instance -> methodDefinition.HasThis

let private describeCandidates candidates =
    candidates
    |> List.map canonicalSelector
    |> List.sort
    |> String.concat Environment.NewLine

let selectMethod (assembly: AssemblyDefinition) (selectorText: string) =
    // 短いメソッド名は利便性のため許すが、一意でない場合は候補を示して厳密指定を要求する。
    let methods = allMethods assembly

    let candidates =
        if selectorText.Contains("::", StringComparison.Ordinal) then
            let selector = parseExactSelector selectorText
            methods
            |> List.filter (fun methodDefinition ->
                methodDefinition.DeclaringType.FullName = selector.TypeName
                && methodDefinition.Name = selector.MethodName
                && dispatchMatches selector.Dispatch methodDefinition
                && (methodDefinition.Parameters
                    |> Seq.map (fun parameter -> parameter.ParameterType.FullName)
                    |> Seq.toList) = selector.ParameterTypes)
        else
            methods
            |> List.filter (fun methodDefinition ->
                methodDefinition.Name = selectorText)

    match candidates with
    | [ methodDefinition ] -> methodDefinition
    | [] ->
        failwithf "メソッド '%s' が見つかりませんでした。" selectorText
    | _ ->
        failwithf
            "メソッド指定 '%s' は曖昧です。次のいずれかを厳密に指定してください:%s%s"
            selectorText
            Environment.NewLine
            (describeCandidates candidates)
