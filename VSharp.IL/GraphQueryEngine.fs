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
        
[<Struct>]
type StartVertex =
    val Vertex: int<inputGraphVertex>
    val HistorySpecificRSMState: Option<int<rsmState>>    
    new (vertex, historySpecificRSMState) =
        {
            Vertex = vertex
            HistorySpecificRSMState = historySpecificRSMState            
        }

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
    
type private CfpqState (query) =
    let mutable gss = GSS()    
    let mutable matchedRanges = MatchedRanges ()
    let computedDistances = ResizeArray<Dictionary<MatchedRange,DistanceInfo>>()    
    let reachableVertices = Dictionary<int<inputGraphVertex>,HashSet<int<inputGraphVertex>>>()
    let mutable query = query
    member this.GSS 
        with get () = gss        
    member this.MatchedRanges
        with get () = matchedRanges        
    member this.ReachableVertices
        with get () = reachableVertices
    member this.Query = query
    member this.ComputedDistances
        with get () = computedDistances            
    member this.Reset _query =
        Logger.trace $"CFQP cache info: computedDistances: %i{computedDistances.Count}"                        
        gss <- GSS()
        query <- _query
        matchedRanges <- MatchedRanges ()        
        reachableVertices.Clear()
        computedDistances.Clear()
        
type GraphQueryEngine() as this =
    let vertices = Dictionary<int<inputGraphVertex>,ResizeArray<InputGraphEdge>>()
    let balancedBracketsRsmBoxStartState = 2<rsmState>
    let balancedBracketsRsmBoxFinalState = 2<rsmState>
    let callImbalanceRsmBoxStartState = 0<rsmState>
    let callImbalanceRsmBoxFinalState = 1<rsmState>
    let historyRsmBoxStartState = 3<rsmState>
    let historyRsmBoxDefaultFinalState = 4<rsmState>
    let historyRsmBoxHistoryStartState = 5<rsmState>
    let mutable firstFreeRsmState = 6<rsmState>
    let terminalForCFGEdge = 0<terminalSymbol>
    let mutable firstFreeCallTerminalId = 1<terminalSymbol>
    let historyRsmBox =
        RSMBox(
            historyRsmBoxStartState,
            HashSet[|historyRsmBoxDefaultFinalState|],
            [|
                RSMEdges.NonTerminalEdge(historyRsmBoxStartState, callImbalanceRsmBoxStartState, historyRsmBoxDefaultFinalState)
                RSMEdges.NonTerminalEdge(historyRsmBoxStartState, balancedBracketsRsmBoxStartState, historyRsmBoxHistoryStartState)
            |]
            )
    let balancedBracketsRsmBox =         
        RSMBox(
            balancedBracketsRsmBoxStartState,
            HashSet[|balancedBracketsRsmBoxFinalState|],
            [|
                TerminalEdge(balancedBracketsRsmBoxStartState,terminalForCFGEdge,balancedBracketsRsmBoxFinalState)
            |]
            )
    let callImbalanceBracketsRsmBox =         
        RSMBox(
            callImbalanceRsmBoxStartState,
            HashSet[|callImbalanceRsmBoxFinalState|],
            [|
                RSMEdges.NonTerminalEdge(callImbalanceRsmBoxStartState, balancedBracketsRsmBoxStartState, callImbalanceRsmBoxFinalState)
            |]
            )
    let getQuery() = RSM([|historyRsmBox; balancedBracketsRsmBox; callImbalanceBracketsRsmBox|], historyRsmBox)
    let finalVertices = ResizeArray<int<inputGraphVertex>>()
    let startVertices = HashSet<StartVertex>()    
    let distancesCache = Dictionary<StartVertex,DistancesStorage>()
    let callEdgeToCallTerminal = Dictionary<Edge,int<terminalSymbol>>()
    let cfpqState = CfpqState(getQuery())
    
    let addReachabilityInfo (startVertices:HashSet<StartVertex>) =        
        if Seq.length startVertices > 0
        then            
            Logger.trace $"GLL started. Vertices in graph: %i{vertices.Count}. States in RSM: %A{cfpqState.Query.StatesCount}. Start vertices count: %A{Seq.length startVertices}."
            let startGLL = System.DateTime.Now
            for vertex in startVertices do
                if not <| distancesCache.ContainsKey vertex
                then
                    let distances = DistancesStorage()                
                    distancesCache.Add(vertex, distances)

            startVertices
            |> Seq.iter (fun (v:StartVertex) ->
                evalFromState cfpqState.ReachableVertices cfpqState.GSS cfpqState.MatchedRanges this (HashSet<_>[|v.Vertex|]) cfpqState.Query Mode.AllPaths
                |> ignore )

            Logger.trace $"GLL finished. GLL running time: %A{(System.DateTime.Now - startGLL).TotalMilliseconds} ms."            
            
    let updateDistances startVertices finalVertices =
        let start = System.DateTime.Now
        startVertices
        |> Seq.iter (fun (v:StartVertex) ->
            let update distances =
                for (distanceInfo:DistanceComputationResult) in distances do
                    match distanceInfo.Distance with            
                    | Reachable d -> distancesCache.[v].AddOrUpdate(distanceInfo.FinalVertex  , d * 1<distance>)
                    | Unreachable -> ()
            let historyIndependentDistances =                
                cfpqState.MatchedRanges.GetShortestDistances(cfpqState.Query, HashSet [|historyRsmBoxDefaultFinalState|], HashSet(), cfpqState.ComputedDistances, v.Vertex, finalVertices)
            update historyIndependentDistances
            
            match v.HistorySpecificRSMState with
            | None -> ()
            | Some p ->
                let historyDependentDistances =                
                    cfpqState.MatchedRanges.GetShortestDistances(cfpqState.Query, cfpqState.Query.OriginalFinalStates, HashSet([|p|]), cfpqState.ComputedDistances, v.Vertex, finalVertices)
                update historyDependentDistances
        )
        Logger.trace $"Distances updated in %A{(System.DateTime.Now - start).TotalMilliseconds} milliseconds."
        
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
        
        callImbalanceBracketsRsmBox.AddTransition(TerminalEdge(callImbalanceRsmBoxFinalState, firstFreeCallTerminalId, callImbalanceRsmBoxStartState))
        
        balancedBracketsRsmBox.AddTransition(TerminalEdge(balancedBracketsRsmBoxStartState, firstFreeCallTerminalId, firstFreeRsmState))
        balancedBracketsRsmBox.AddTransition(NonTerminalEdge(firstFreeRsmState, balancedBracketsRsmBoxStartState, firstFreeRsmState + 1<rsmState>))
        balancedBracketsRsmBox.AddTransition(TerminalEdge(firstFreeRsmState + 1<rsmState>, firstFreeCallTerminalId + 1<terminalSymbol>, balancedBracketsRsmBoxFinalState))
        
        firstFreeRsmState <- firstFreeRsmState + 2<rsmState>
        
        for edge:Edge in returnEdges do    
            InputGraphEdge(firstFreeCallTerminalId + 1<terminalSymbol>, edge.FinalVertex)
            |> vertices.[edge.StartVertex].Add
            
        firstFreeCallTerminalId <- firstFreeCallTerminalId + 2<terminalSymbol>        
        cfpqState.Reset (getQuery())
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
    
    member this.AddHistoryStep (previousStartVertex:StartVertex, newCallTerminal:int<terminalSymbol>) =
        let returnSymbol = newCallTerminal + 1<terminalSymbol>
        //cfpqState.Query.ToDot "rsm.dot"
        match previousStartVertex.HistorySpecificRSMState with
        | Some specificPoint -> 
            let previousReturn = (historyRsmBox.IncomingEdges specificPoint).[0].Terminal                
            
            let suchStepExists =
                historyRsmBox.OutgoingEdges historyRsmBoxHistoryStartState
                |> ResizeArray.tryFind                 
                    (
                      fun e ->
                          match e with 
                          | TerminalEdge (_from,_t,_to) ->
                               _t = returnSymbol
                               && (historyRsmBox.OutgoingEdges (_to + 1<rsmState>)).[0].Terminal = previousReturn
                          | _ -> failwith "Inconsistent history RSM.")
            
            let newSpecificPoint = 
                if suchStepExists.IsNone
                then
                    let mergePoint = specificPoint + 1<rsmState>                        
                    historyRsmBox.AddTransition (TerminalEdge(historyRsmBoxHistoryStartState, returnSymbol, firstFreeRsmState))
                    historyRsmBox.AddTransition (NonTerminalEdge(firstFreeRsmState, balancedBracketsRsmBoxStartState, firstFreeRsmState + 1<rsmState>))
                    historyRsmBox.AddTransition (TerminalEdge(firstFreeRsmState + 1<rsmState>, previousReturn, firstFreeRsmState + 2<rsmState>))
                    historyRsmBox.AddTransition (NonTerminalEdge(firstFreeRsmState + 2<rsmState>, balancedBracketsRsmBoxStartState, mergePoint))
                    let added = historyRsmBox.FinalStates.Add (firstFreeRsmState + 1<rsmState>)
                    assert added
                    firstFreeRsmState <- firstFreeRsmState + 3<rsmState>
                    firstFreeRsmState - 3<rsmState>
                else
                    suchStepExists.Value.FinalState
                    
            Some newSpecificPoint
        | None ->
            historyRsmBox.AddTransition (TerminalEdge(historyRsmBoxHistoryStartState, returnSymbol, firstFreeRsmState))
            historyRsmBox.AddTransition (NonTerminalEdge(firstFreeRsmState, balancedBracketsRsmBoxStartState, firstFreeRsmState + 1<rsmState>))
            let added = historyRsmBox.FinalStates.Add (firstFreeRsmState + 1<rsmState>)
            assert added
            firstFreeRsmState <- firstFreeRsmState + 2<rsmState>
            Some (firstFreeRsmState - 2<rsmState>)

    member this.PopHistoryStep (startVertex:StartVertex) =
        //getQuery().ToDot "rsm.dot"
        match startVertex.HistorySpecificRSMState with
        | Some specificPoint ->
            let outgoingEdges = historyRsmBox.OutgoingEdges (specificPoint + 1<rsmState>) 
            if outgoingEdges.Count = 1
            then
                let previousReturn = outgoingEdges.[0].Terminal            
                let newSpecificPoint =
                    let possibleNewHeads =
                        historyRsmBox.OutgoingEdges historyRsmBoxHistoryStartState
                        |> ResizeArray.filter (fun e -> e.Terminal = previousReturn)            
                    if possibleNewHeads.Count = 1
                    then possibleNewHeads.[0].FinalState
                    else
                        let mergePoint = (historyRsmBox.OutgoingEdges (specificPoint + 2<rsmState>)).[0].FinalState
                        possibleNewHeads
                        |> ResizeArray.find (fun e -> (historyRsmBox.OutgoingEdges e.FinalState).[0].FinalState = mergePoint)
                        |> fun x -> x.FinalState
                Some newSpecificPoint
            else None
        | None -> failwith "Pop from empty history."
        
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