namespace VSharp

open System
open System.Collections.Generic
open System.Reflection
open System.Reflection.Emit
open VSharp.CSharpUtils

module AssemblyManager =
    let mutable private alc = new VSharpAssemblyLoadContext("vsharp_alc_0")

    let mutable private alcVersion = 0

    let GetAssemblies() =
        alc.Assemblies

    let SetDependenciesDirs (dirs : IEnumerable<string>) =
        alc.DependenciesDirs = dirs

    let AddExtraResolver (resolver : Func<string, string>) =
        alc.add_ExtraResolver resolver

    let RemoveExtraResolver (resolver : Func<string, string>) =
        alc.remove_ExtraResolver resolver

    let LoadFromAssemblyPath (assemblyPath : string) =
        try 
            alc.LoadFromAssemblyPath assemblyPath
        with
        | e ->
            alc.Unload()
            reraise()
    let LoadCopy (assembly : Assembly) =
        try
            alc.LoadFromAssemblyPath(assembly.Location)
        with
        | e ->
            alc.Unload()
            reraise()

    let LoadFromAssemblyName (assemblyName : string) =
        try
            alc.LoadFromAssemblyName(AssemblyName(assemblyName))
        with
        | e ->
            alc.Unload()
            reraise()

    let NormalizeType (t : Type) =
        try
            alc.NormalizeType(t)
        with
        | e ->
            alc.Unload()
            reraise()

    let NormalizeMethod (m : MethodBase) =
        try
            alc.NormalizeMethod(m)
        with
        | e ->
            alc.Unload()
            reraise()

    // Used in tests to reset the state. For example, in tests Veritas.
    // A more correct approach is to inject a VSharpAssemblyLoadContext instance
    // into all places of use via the constructor.
    // But there are no resources for this approach.
    //
    // WARNING: Using this method doesn't guarantee that types and methods associated
    // with current context won't appear during further execution -- because of global
    // caches, like terms hash map and Application. Particularly, types with the same names
    // from different contexts may appear (and don't be equal)
    let Reset() =
        alcVersion <- alcVersion + 1
        alc.Dispose()
        alc <- new VSharpAssemblyLoadContext("vsharp_alc_" + alcVersion.ToString())

    let DefineDynamicAssembly (name : AssemblyName, access : AssemblyBuilderAccess) =
        using (alc.EnterContextualReflection()) (fun _ -> AssemblyBuilder.DefineDynamicAssembly(name, access))
