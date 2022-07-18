namespace VSharp.Interpreter.IL

open System
open System.Collections.Generic
open System.Diagnostics
open System.IO
open VSharp
open VSharp.Core

type DotVisualizer(graph : ApplicationGraph, outputDirectory : DirectoryInfo) =
    let dotPath = Environment.GetEnvironmentVariable("DOT_PATH")
    let dotPath = if String.IsNullOrWhiteSpace dotPath then "dot" else dotPath
    let dotFile = Path.GetTempFileName()
    let outputDirectory = outputDirectory.CreateSubdirectory("visualization")
    let ids = Dictionary<codeLocation, string>()
    let mutable lastVertexId = 0
    let mutable lastPictureId = 0
    let stateMarkers = Dictionary<codeLocation, int>()
    let visitedVertices = HashSet<codeLocation>()
    let visitedEdges = HashSet<codeLocation * codeLocation>()

    let leave loc =
        stateMarkers.[loc] <- stateMarkers.[loc] - 1
    let visit loc =
        visitedVertices.Add loc |> ignore
        if stateMarkers.ContainsKey loc then stateMarkers.[loc] <- stateMarkers.[loc] + 1
        else stateMarkers.Add(loc, 1)
    let move fromLoc toLoc =
        visit toLoc
        visitedEdges.Add(fromLoc, toLoc) |> ignore

    let id loc = Dict.getValueOrUpdate ids loc (fun () -> lastVertexId <- lastVertexId + 1; $"v{lastVertexId}")
    let visitedColor = "#D3D3D3B4"
    let unvisitedColor = "#000000"
    let colorOfNode loc =
        let markers = Dict.tryGetValue stateMarkers loc 0
        if markers > 0 then
            let alpha = 256 - 128 / (1 <<< (min 7 markers))
            let r, g, b = 0xCC, 0x88, 0x99
            sprintf "#%x%x%x%x" r g b alpha, "filled"
        elif visitedVertices.Contains loc then visitedColor, "filled"
        else unvisitedColor, "\"\""
    let colorOfEdge fromLoc toLoc =
        if visitedEdges.Contains(fromLoc, toLoc) then visitedColor else unvisitedColor

    let node (cfg : CfgInfo) loc =
        let color, style = colorOfNode loc
        let text = (cfg.BasicBlockToString loc.offset |> join "\\l") + "\\l"
        $"{id loc} [shape=ellipse, label=\"{text}\", color=\"{color}\", style={style}]"
    let edge fromLoc toLoc =
        $"{id fromLoc} -> {id toLoc} [color=\"{colorOfEdge fromLoc toLoc}\"]"

    let cfgToDot (cfg : CfgInfo) =
        seq{
            let name = cfg.MethodBase.Name // TODO: declaring type & overloads!
            yield $"subgraph cluster_%s{name} {{"
            yield $"label=%A{name}"
            for vertex in cfg.SortedOffsets do
                yield node cfg {method = cfg.MethodBase; offset = vertex}
            for kvp in cfg.Edges do
                let from = {method = cfg.MethodBase; offset = kvp.Key}
                for toOffset in kvp.Value do
                    let toLoc = {method = cfg.MethodBase; offset = toOffset}
                    yield edge from toLoc
            yield "}"
        }

    member private x.Compile() =
        lastPictureId <- lastPictureId + 1
        let format = "0000000000"
        let output = $"{outputDirectory.FullName}{Path.DirectorySeparatorChar}Step{lastPictureId.ToString(format)}.png"
        let startInfo = ProcessStartInfo()
        startInfo.FileName <- dotPath
        startInfo.Arguments <- $"-Tpng {dotFile} -o {output}"
        Process.Start(startInfo) |> ignore

    interface IVisualizer with

        override x.AddMarker loc = visit loc

        override x.VisualizeGraph () =
            let dot = seq {
               yield "digraph G"
               yield "{"
               for cfg in graph.CFGs do
                   yield! cfgToDot cfg
               yield "}"
            }
            File.WriteAllLines(dotFile, dot)
            x.Compile()

        override x.VisualizeStep fromLoc toLoc newMarkers =
            leave fromLoc
            move fromLoc toLoc
            newMarkers |> Seq.iter (move fromLoc)
            (x :> IVisualizer).VisualizeGraph()
