module CilFrontend.CilTypes

open System
open Mono.Cecil
open Mono.Cecil.Cil

let isIntegerType (t: TypeReference) =
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

let isStringType (t: TypeReference) =
    t.FullName = "System.String"

let isListType (t: TypeReference) =
    t.FullName.StartsWith("Microsoft.FSharp.Collections.FSharpList`1", StringComparison.Ordinal)

let isGenericListType (t: TypeReference) =
    t.FullName.StartsWith("System.Collections.Generic.List`1", StringComparison.Ordinal)
    && not (t.FullName.Contains("/Enumerator", StringComparison.Ordinal))

let isGenericListEnumeratorType (t: TypeReference) =
    t.FullName.StartsWith("System.Collections.Generic.List`1/Enumerator", StringComparison.Ordinal)

let isArrayType (t: TypeReference) = t.IsArray

let sizeVariableName name = name + "_length"

let argumentName (method: MethodDefinition) index =
    if method.HasThis then
        if index = 0 then "this"
        else method.Parameters[index - 1].Name
    else method.Parameters[index].Name

let parameterName (parameter: ParameterDefinition) =
    if String.IsNullOrWhiteSpace parameter.Name then sprintf "arg%d" parameter.Index
    else parameter.Name

let localName (variable: VariableDefinition) = sprintf "loc%d" variable.Index
