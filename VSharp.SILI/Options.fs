namespace VSharp.Interpreter.IL

open System.Diagnostics
open System.IO

type searchMode =
    | DFSMode
    | BFSMode

type coverageZone =
    | MethodZone
    | ClassZone
    | ModuleZone

type explorationMode =
    | TestCoverageMode of coverageZone * searchMode
    | StackTraceReproductionMode of StackTrace

type executionMode =
    | ConcolicMode
    | SymbolicMode

type SiliOptions = {
    explorationMode : explorationMode
    executionMode : executionMode
    outputDirectory : DirectoryInfo
    bound : uint32
    visualize : bool
}
