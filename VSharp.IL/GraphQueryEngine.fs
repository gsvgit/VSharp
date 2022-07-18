namespace VSharp

open System.Collections.Generic
open CFPQ_GLL.GLL
open CFPQ_GLL.GSS
open CFPQ_GLL.InputGraph
open CFPQ_GLL.RSM
open CFPQ_GLL.SPPF
open FSharpx.Collections

type [<Measure>] distance

type private DistancesStorage () =
    let distances = Dictionary<int<inputGraphVertex>,int<distance>>()
    let mutable nearestVertex = None
    
    let updateNearestVertex newVertex newDistance =
        match nearestVertex with
        | None -> nearestVertex <- Some (newVertex, newDistance)
        | Some (vertex, distance) ->
            if newDistance < distance
            then nearestVertex <- Some (newVertex, newDistance)
            
    member this.GetNearestVertex () =
        match nearestVertex with
        | Some x -> Some x
        | None ->
            if distances.Count = 0
            then None
            else failwith "Inconsistent state of distances storage."
    
    member this.Update (vertex:int<inputGraphVertex>, distance:int<distance>) =
        assert (distances.ContainsKey vertex)
        updateNearestVertex vertex distance
        distances.[vertex] <- distance
        
    member this.Add (vertex:int<inputGraphVertex>, distance:int<distance>) =
        assert (not <| distances.ContainsKey vertex)
        updateNearestVertex vertex distance
        distances.Add(vertex, distance)
        
    member this.AddOrUpdate (vertex:int<inputGraphVertex>, distance:int<distance>) =        
        updateNearestVertex vertex distance
        if distances.ContainsKey vertex
        then distances.[vertex] <- distance
        else distances.Add(vertex, distance)
        
    member this.Remove (vertexToRemove:int<inputGraphVertex>) =
        match nearestVertex with
        | Some (vertex,_) ->
            if vertex = vertexToRemove
            then nearestVertex <- None
        | None -> failwith "Inconsistent state of distances storage."
        let removed = distances.Remove vertexToRemove
        assert removed
        for kvp in distances do
            updateNearestVertex kvp.Key kvp.Value
        
type CallHistory = list<int<terminalSymbol>>

[<Struct>]
type StartVertex =
    val Vertex: int<inputGraphVertex>
    val CallHistory: CallHistory
    new (vertex, callHistory) = {Vertex = vertex; CallHistory = callHistory}

[<Struct>]
type Cluster =
    val Name: string
    val Vertices: seq<int<inputGraphVertex>>
    new (name, vertices) = {Name = name; Vertices = vertices}

[<Struct>]
type Edge =
    val StartVertex: int<inputGraphVertex>
    val FinalVertex: int<inputGraphVertex>
    new (startVertex, finalVertex) = {StartVertex = startVertex; FinalVertex = finalVertex}
    
type private CfpqState (terminalForCFGEdge, firstFreeCallTerminalId) =
    let mutable gss = GSS()    
    let mutable matchedRanges = MatchedRanges ()
    let computedDistances = Dictionary<MatchedRange,int>()    
    let reachableVertices = Dictionary<int<inputGraphVertex>,HashSet<int<inputGraphVertex>>>()
    let historyToQuery = Dictionary<list<int<terminalSymbol>>,RSM>()
    let mutable firstFreeRsmState = 3<rsmState>
    let mutable _balancedBracketsBox = Unchecked.defaultof<RSMBox>
    let mutable _baseQueryStartBox = Unchecked.defaultof<RSMBox>
    
    let buildQuery firstFreeCallTerminalId =
        let startBox =
            RSMBox(
                0<rsmState>,
                HashSet [|1<rsmState>|],
                [|                    
                    yield RSMEdges.NonTerminalEdge(0<rsmState>, 2<rsmState>, 1<rsmState>)                    
                    for callSymbol in 1<terminalSymbol> .. 2<terminalSymbol> .. firstFreeCallTerminalId - 1<terminalSymbol> do
                      yield RSMEdges.TerminalEdge(1<rsmState>, callSymbol, 0<rsmState>)
                |]
                )
        let balancedBracketsBox =          
          RSMBox(
              2<rsmState>,
              HashSet [|2<rsmState>|],
              [|
                  yield RSMEdges.TerminalEdge (2<rsmState>, terminalForCFGEdge, 2<rsmState>)
                  for callSymbol in 1<terminalSymbol> .. 2<terminalSymbol> .. firstFreeCallTerminalId - 1<terminalSymbol> do
                      yield RSMEdges.TerminalEdge(2<rsmState>, callSymbol, firstFreeRsmState)
                      yield RSMEdges.NonTerminalEdge(firstFreeRsmState, 2<rsmState>, firstFreeRsmState + 1<rsmState>)
                      yield RSMEdges.TerminalEdge(firstFreeRsmState + 1<rsmState>, callSymbol + 1<terminalSymbol>, 2<rsmState>)                  
                      firstFreeRsmState <- firstFreeRsmState + 2<rsmState>
          |])
        _balancedBracketsBox <- balancedBracketsBox
        _baseQueryStartBox <- startBox
        RSM([|startBox; balancedBracketsBox|], startBox)
    
    let mutable baseQuery = buildQuery firstFreeCallTerminalId
    
    
    let buildQueryWithHistory history =
        let exists, query = historyToQuery.TryGetValue history
        if exists
        then query
        else
            let startBox =
                RSMBox (
                    firstFreeRsmState,
                    HashSet<_>([|for i in 1 .. history.Length + 2 -> firstFreeRsmState + i * 1<rsmState>|]),
                    [|
                        yield RSMEdges.NonTerminalEdge(firstFreeRsmState, 0<rsmState>, firstFreeRsmState + 1<rsmState>)
                        yield RSMEdges.NonTerminalEdge(firstFreeRsmState, 2<rsmState>, firstFreeRsmState + 2<rsmState>)
                        firstFreeRsmState <- firstFreeRsmState + 2<rsmState>
                        for h in history do
                            yield RSMEdges.TerminalEdge(firstFreeRsmState, h + 1<terminalSymbol>, firstFreeRsmState + 1<rsmState>)
                            yield RSMEdges.NonTerminalEdge(firstFreeRsmState + 1<rsmState>, 2<rsmState>, firstFreeRsmState + 2<rsmState>)
                            firstFreeRsmState <- firstFreeRsmState + 2<rsmState>
                    |]                    
                    )
            let rsm = RSM([|startBox; _balancedBracketsBox; _baseQueryStartBox|], startBox)
            historyToQuery.Add (history, rsm)
            //rsm.ToDot "rsm.dot"
            rsm
    
    member this.GSS 
        with get () = gss        
    member this.MatchedRanges
        with get () = matchedRanges        
    member this.ReachableVertices
        with get () = reachableVertices
    member this.BaseQuery = baseQuery
    member this.HistoryToQuery = historyToQuery
    member this.ComputedDistances
        with get () = computedDistances    
    member this.BuildQueryWithHistory history = buildQueryWithHistory history    
    member this.Reset firstFreeCallTerminalId =
        Logger.trace $"CFQP cache info: historyToQuery: %i{historyToQuery.Count}, computedDistances: %i{computedDistances.Count}"
        firstFreeRsmState <- 3<rsmState>
        baseQuery <- buildQuery firstFreeCallTerminalId        
        gss <- GSS()
        matchedRanges <- MatchedRanges ()
        historyToQuery.Clear()
        reachableVertices.Clear()
        computedDistances.Clear()
        

type GraphQueryEngine() as this =
    let vertices = Dictionary<int<inputGraphVertex>,ResizeArray<InputGraphEdge>>()
    let terminalForCFGEdge = 0<terminalSymbol>
    let mutable firstFreeCallTerminalId = 1<terminalSymbol>
    let finalVertices = ResizeArray<int<inputGraphVertex>>()
    let startVertices = HashSet<StartVertex>()    
    let distancesCache = Dictionary<StartVertex,DistancesStorage>()
    let callEdgeToCallTerminal = Dictionary<Edge,int<terminalSymbol>>()
    let cfpqState = CfpqState(terminalForCFGEdge, firstFreeCallTerminalId)
    
    let addReachabilityInfo (startVertices:HashSet<StartVertex>) =        
        if Seq.length startVertices > 0
        then            
            Logger.trace $"GLL started. Vertices in graph: %i{vertices.Count}. Start vertices count: %A{Seq.length startVertices}."
            let startGLL = System.DateTime.Now
            for vertex in startVertices do
                if not <| distancesCache.ContainsKey vertex
                then
                    let distances = DistancesStorage()                
                    distancesCache.Add(vertex, distances)
                    
            startVertices
            |> Seq.iter (fun (v:StartVertex) ->
                evalFromState cfpqState.ReachableVertices cfpqState.GSS cfpqState.MatchedRanges this (HashSet<_>[|v.Vertex|]) (cfpqState.BuildQueryWithHistory v.CallHistory) Mode.AllPaths
                |> ignore )

            Logger.trace $"GLL finished. GLL running time: %A{(System.DateTime.Now - startGLL).TotalMilliseconds} ms."            
            
    let updateDistances startVertices finalVertices =        
        startVertices
        |> Seq.iter (fun (v:StartVertex) -> 
            let distances =
                //Logger.trace $"Original final states: %A{cfpqState.HistoryToQuery.[v.CallHistory].OriginalFinalStates}"
                cfpqState.MatchedRanges.GetShortestDistances(cfpqState.HistoryToQuery.[v.CallHistory], cfpqState.ComputedDistances, [|v.Vertex|], finalVertices)
            for _from,_to,distance in distances do
                match distance with            
                | Reachable d -> distancesCache.[v].AddOrUpdate(_to, d * 1<distance>)
                | Unreachable -> ()
        )
        
    let addCfgEdge (edge:Edge) =
        let exists, outgoingEdges = vertices.TryGetValue edge.StartVertex
        let newEdge = InputGraphEdge(terminalForCFGEdge, edge.FinalVertex)
        if exists
        then outgoingEdges.Add newEdge
        else vertices.Add(edge.StartVertex, ResizeArray<_>[|newEdge|])
        if not <| vertices.ContainsKey edge.FinalVertex
        then vertices.Add(edge.FinalVertex, ResizeArray<_>())        
        
    let addVertices newVertices =
        for v in newVertices do
            if not <| vertices.ContainsKey v
            then vertices.Add(v,ResizeArray<_>())
        
    let addStartVertices (vertices: array<StartVertex>) =        
        startVertices.UnionWith (HashSet vertices)
        let verticesToUpdate = vertices |> Array.filter (fun v -> not <| distancesCache.ContainsKey v)
        if verticesToUpdate.Length > 0
        then 
            addReachabilityInfo (HashSet<_> verticesToUpdate)
            updateDistances verticesToUpdate finalVertices
        
    let addFinalVertices (vertices:seq<int<inputGraphVertex>>) =
        let newFinalVertices = ResizeArray<_>()
        for v in vertices do
            finalVertices.Add v
            newFinalVertices.Add v                
        updateDistances startVertices newFinalVertices
        
    let removeFinalVertex (vertex:int<inputGraphVertex>) =
        let removed = finalVertices.Remove vertex
        assert removed
        for kvp in distancesCache do            
            kvp.Value.Remove vertex 
    
    interface IInputGraph with
        member this.GetOutgoingEdges v =
            vertices.[v]        
    
    member this.AddVertices vertices = addVertices vertices
    
    member this.AddCfgEdge edge = addCfgEdge edge
        
    member this.AddCfgEdges edges = Seq.iter addCfgEdge edges
    
    member this.RemoveCfgEdge (edge:Edge) =
        let removed = vertices.[edge.StartVertex].Remove(InputGraphEdge(terminalForCFGEdge, edge.FinalVertex))
        assert removed
            
    member this.AddCallReturnEdges (callEdge:Edge, returnEdges) =
        InputGraphEdge(firstFreeCallTerminalId, callEdge.FinalVertex)
        |> vertices.[callEdge.StartVertex].Add
        
        callEdgeToCallTerminal.Add(callEdge, firstFreeCallTerminalId)
        
        for edge:Edge in returnEdges do    
            InputGraphEdge(firstFreeCallTerminalId + 1<terminalSymbol>, edge.FinalVertex)
            |> vertices.[edge.StartVertex].Add
            
        firstFreeCallTerminalId <- firstFreeCallTerminalId + 2<terminalSymbol>
        cfpqState.Reset firstFreeCallTerminalId
        distancesCache.Clear()
        addReachabilityInfo startVertices
        updateDistances startVertices finalVertices

    member this.AddFinalVertex vertex = addFinalVertices [|vertex|]
        
    member this.AddFinalVertices vertices = addFinalVertices vertices
    
    member this.RemoveFinalVertex vertex = removeFinalVertex vertex
    
    member this.AddStartVertex vertex = addStartVertices [|vertex|]
    
    member this.AddStartVertices vertices = addStartVertices vertices
    
    member this.RemoveStartVertex vertex =
        let removed = startVertices.Remove vertex
        assert removed
        
    member this.GetDistanceToNearestGoal startVertex =
        distancesCache.[startVertex].GetNearestVertex()
    
    member this.GetTerminalForCallEdge edge = callEdgeToCallTerminal.[edge]
    
    member this.ToDot (clusters, filePath) =
        let subgraphs =
            seq{
                for cluster:Cluster in clusters do
                    yield $"subgraph cluster_%s{cluster.Name} {{"
                    yield $"label=%A{cluster.Name}"                    
                    for vertex in cluster.Vertices do
                        yield string vertex
                    yield "}"  
            }
                       
        let content =
            seq{
               yield "digraph G"
               yield "{"
               yield "node [shape = plaintext]"
               yield! subgraphs
               for kvp in vertices do
                for e in kvp.Value do
                    yield $"%i{kvp.Key} -> %i{e.TargetVertex} [label=%A{e.TerminalSymbol}]"
               yield "}"
            }
        
        System.IO.File.WriteAllLines(filePath, content)