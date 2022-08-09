namespace VSharp

open CFPQ_GLL.Common
open global.System
open System.Reflection
open System.Collections.Generic
open CFPQ_GLL.InputGraph
open FSharpx.Collections
open Microsoft.FSharp.Collections
open VSharp

[<Struct>]
type internal temporaryCallInfo = {callee: MethodWithBody; callFrom: offset; returnTo: offset}

type BasicBlock (method: MethodWithBody, startOffset: offset) =
    inherit InputGraphVertexBase ()    
    let mutable finalOffset = None
    let incomingEdges = HashSet<BasicBlock>()
    member this.StartOffset = startOffset
    member this.Method = method
    member this.OutgoingEdges = (this :> InputGraphVertexBase :> IInputGraphVertex).OutgoingEdges
    member this.IncomingEdges = incomingEdges
    member this.HasSiblings
        with get () =
            let siblings = HashSet<IInputGraphVertex>()
            for bb in incomingEdges do
                for kvp in bb.OutgoingEdges do
                    siblings.UnionWith kvp.Value
            siblings.Count > 1

    member this.FinalOffset
        with get () =
                match finalOffset with
                | Some v -> v
                | None -> failwith "Final vertex of this basic block is not specified yet."
        and set (v: offset) = finalOffset <- Some v
        
    member this.ToString () =
        let parsedInstructions = method.ParsedInstructions
        let mutable instr = parsedInstructions |> Array.find (fun instr -> Offset.from (int instr.offset) = this.StartOffset)
        let endInstr = parsedInstructions |> Array.find (fun instr -> Offset.from (int instr.offset) = this.FinalOffset)            
        seq {
            while not <| LanguagePrimitives.PhysicalEquality instr endInstr do
                yield ILRewriter.PrintILInstr None None method.MethodBase instr
                instr <- instr.next
        }

[<Struct>]
type CallInfo =
    val Callee: Method
    val CallFrom: offset
    val ReturnTo: offset
    new (callee, callFrom, returnTo) =
        {
            Callee = callee
            CallFrom = callFrom
            ReturnTo = returnTo
        }

and CfgInfo internal (method : MethodWithBody) =
    let () = assert method.HasBody    
    let ilBytes = method.ILBytes
    let exceptionHandlers = method.ExceptionHandlers
    let sortedBasicBlocks = ResizeArray<BasicBlock>()    
    let sinks = ResizeArray<_>()
    let calls = Dictionary<_,_>()
    let loopEntries = HashSet<offset>()
    let terminalForCFGEdge = 0<terminalSymbol>

    let dfs (startVertices : array<offset>) (*exceptionHandlingEntries: array<offset>*) =
        let used = HashSet<offset>()
        let basicBlocks = HashSet<BasicBlock> (Array.map (fun v -> BasicBlock(method,v)) startVertices)
        let addBasicBlock v = basicBlocks.Add v |> ignore
        let greyVertices = HashSet<offset>()
        let vertexToBasicBlock: array<Option<BasicBlock>> = Array.init ilBytes.Length (fun _ -> None)

        let splitBasicBlock (block:BasicBlock) intermediatePoint =
            let newBlock = BasicBlock (method, intermediatePoint)
            newBlock.FinalOffset <- block.FinalOffset            
            for v in int intermediatePoint .. int block.FinalOffset  do
                vertexToBasicBlock.[v] <- Some newBlock
            block.FinalOffset <- intermediatePoint
            let finalVertex =
                (vertexToBasicBlock |> Array.findIndexBack (fun b -> b.IsSome && b.Value = block))
                 * 1<offsets>
            block.FinalOffset <- finalVertex
            for kvp in block.OutgoingEdges do
                newBlock.OutgoingEdges.Add(kvp.Key, kvp.Value)
            block.OutgoingEdges.Clear()
            block.OutgoingEdges.Add(terminalForCFGEdge, HashSet[|newBlock :> InputGraphVertexBase :> IInputGraphVertex|])
            newBlock
            
        let makeNewBasicBlock startVertex =
            match vertexToBasicBlock.[int startVertex] with
            | None ->
                let newBasicBlock = BasicBlock (method, startVertex)
                addBasicBlock newBasicBlock
                newBasicBlock
            | Some block ->
                if block.StartOffset = startVertex
                then block
                else splitBasicBlock block startVertex

        let addEdge (src:BasicBlock) (dst:BasicBlock) =
            let srcGraphVertex = src :> InputGraphVertexBase :> IInputGraphVertex
            let dstGraphVertex = dst :> InputGraphVertexBase :> IInputGraphVertex
            let added = dst.IncomingEdges.Add src
            assert added
            let exists, edges = srcGraphVertex.OutgoingEdges.TryGetValue terminalForCFGEdge 
            if exists
            then
                let added = edges.Add dstGraphVertex
                assert added
            else
                srcGraphVertex.OutgoingEdges.Add(terminalForCFGEdge, HashSet [|dstGraphVertex|])

        let rec dfs' (currentBasicBlock : BasicBlock) (currentVertex : offset) =

            vertexToBasicBlock.[int currentVertex] <- Some currentBasicBlock

            if used.Contains currentVertex
            then                
                if greyVertices.Contains currentVertex
                then loopEntries.Add currentVertex |> ignore
            else
                greyVertices.Add currentVertex |> ignore
                used.Add currentVertex |> ignore
                let opCode = MethodBody.parseInstruction method currentVertex

                let dealWithJump srcBasicBlock dst =
                    let newBasicBlock = makeNewBasicBlock dst 
                    addEdge srcBasicBlock newBasicBlock
                    dfs' newBasicBlock  dst

                let processCall (callee: MethodWithBody) callFrom returnTo =
                    calls.Add(callFrom, CallInfo(callee :?> Method, callFrom, returnTo)) 
                    currentBasicBlock.FinalOffset <- callFrom
                    let newBasicBlock = makeNewBasicBlock returnTo 
                    addEdge currentBasicBlock newBasicBlock
                    dfs' newBasicBlock returnTo

                let ipTransition = MethodBody.findNextInstructionOffsetAndEdges opCode ilBytes currentVertex

                match ipTransition with
                | FallThrough offset when MethodBody.isDemandingCallOpCode opCode ->
                    let opCode', calleeBase = method.ParseCallSite currentVertex
                    assert (opCode' = opCode)
                    let callee = MethodWithBody.InstantiateNew calleeBase
                    if callee.HasBody
                    then processCall callee currentVertex offset
                    else
                        currentBasicBlock.FinalOffset <- offset
                        dfs' currentBasicBlock offset
                | FallThrough offset ->
                    currentBasicBlock.FinalOffset <- offset
                    dfs' currentBasicBlock offset
                | ExceptionMechanism ->
                    ()
                | Return ->
                    sinks.Add currentBasicBlock
                    currentBasicBlock.FinalOffset <- currentVertex
                | UnconditionalBranch target ->
                    currentBasicBlock.FinalOffset <- currentVertex
                    dealWithJump currentBasicBlock target
                | ConditionalBranch (fallThrough, offsets) ->
                    currentBasicBlock.FinalOffset <- currentVertex
                    dealWithJump currentBasicBlock fallThrough
                    offsets |> List.iter (dealWithJump currentBasicBlock)

                greyVertices.Remove currentVertex |> ignore

        startVertices
        |> Array.iter (fun v -> dfs' (BasicBlock (method,v)) v)

        basicBlocks
        |> Seq.sortBy (fun b -> b.StartOffset)
        |> Seq.iter sortedBasicBlocks.Add

    let cfgDistanceFrom = GraphUtils.distanceCache<offset>()

    let findDistanceFrom node =
        Dict.getValueOrUpdate cfgDistanceFrom node (fun () ->
        let dist = Dictionary<_,_>() //GraphUtils.incrementalSourcedDijkstraAlgo node edges cfgDistanceFrom
        let distFromNode = Dictionary<offset, uint>()
        for i in dist do
            if i.Value <> GraphUtils.infinity then
                distFromNode.Add(i.Key, i.Value)
        distFromNode)
    
    let resolveBasicBlockIndex offset =
        let rec binSearch (sortedOffsets : ResizeArray<BasicBlock>) offset l r =
            if l >= r then l
            else
                let mid = (l + r) / 2
                let midValue = sortedOffsets.[mid].StartOffset
                let leftIsLefter = midValue <= offset
                let rightIsRighter = mid + 1 >= sortedOffsets.Count || sortedOffsets.[mid + 1].StartOffset > offset
                if leftIsLefter && rightIsRighter then mid
                elif not rightIsRighter
                    then binSearch sortedOffsets offset (mid + 1) r
                    else binSearch sortedOffsets offset l (mid - 1)

        binSearch sortedBasicBlocks offset 0 (sortedBasicBlocks.Count - 1)

    let resolveBasicBlock offset = sortedBasicBlocks.[resolveBasicBlockIndex offset]

    do
        let startVertices =
            [|
             yield 0<offsets>
             for handler in exceptionHandlers do
                 yield handler.handlerOffset
                 match handler.ehcType with
                 | ehcType.Filter offset -> yield offset
                 | _ -> ()
            |]

        dfs startVertices
    
    member this.SortedBasicBlocks = sortedBasicBlocks
    member this.Sinks = sinks
    member this.Calls = calls
    member this.IsLoopEntry offset = loopEntries.Contains offset
    member internal this.ResolveBasicBlockIndex offset = resolveBasicBlockIndex offset
    member this.ResolveBasicBlock offset = resolveBasicBlock offset
    member this.IsBasicBlockStart offset = (resolveBasicBlock offset).StartOffset = offset
    // Returns dictionary of shortest distances, in terms of basic blocks (1 step = 1 basic block transition)
    member this.DistancesFrom offset =
        let bb = resolveBasicBlock offset
        findDistanceFrom bb.StartOffset
    member this.HasSiblings offset =
        let basicBlock = resolveBasicBlock offset
        basicBlock.StartOffset = offset
        && basicBlock.HasSiblings

and Method internal (m : MethodBase) as this =
    inherit MethodWithBody(m)
    let cfg = lazy(
        if this.HasBody then
            Logger.trace $"Add CFG for {this}."
            //let cfg = CfgTemporaryData this
            Method.ReportCFGLoaded this
            this |> CfgInfo |> Some
        else None)

    member this.IsStaticConstructor = Reflection.isStaticConstructor m
    
    member x.CFG with get() =
        match cfg.Force() with
        | Some cfg -> cfg
        | None -> internalfailf $"Getting CFG of method {x} without body (extern or abstract)"

    // Helps resolving cyclic dependencies between Application and MethodWithBody
    [<DefaultValue>] static val mutable private cfgReporter : Method -> unit
    static member internal ReportCFGLoaded with get() = Method.cfgReporter and set v = Method.cfgReporter <- v

[<CustomEquality; CustomComparison>]
type public codeLocation = {offset : offset; method : Method}
    with
    override x.Equals y =
        match y with
        | :? codeLocation as y -> x.offset = y.offset && x.method.Equals(y.method)
        | _ -> false
    override x.GetHashCode() = (x.offset, x.method).GetHashCode()
    override x.ToString() = sprintf "[method = %s\noffset = %s]" x.method.FullName ((int x.offset).ToString("X"))
    interface IComparable with
        override x.CompareTo y =
            match y with
            | :? codeLocation as y when x.method.Equals(y.method) -> compare x.offset y.offset
            | :? codeLocation as y -> (x.method :> IComparable).CompareTo(y.method)
            | _ -> -1

type IGraphTrackableState =
    abstract member CodeLocation: codeLocation
    abstract member CallStack: list<Method>

type private ApplicationGraphMessage =
    | ResetQueryEngine
    | AddGoals of array<codeLocation>
    | RemoveGoal of codeLocation
    | SpawnStates of seq<IGraphTrackableState>
    | AddForkedStates of parentState:IGraphTrackableState * forkedStates:seq<IGraphTrackableState>
    | MoveState of positionForm:codeLocation * positionTo: IGraphTrackableState
    | RegisterMethod of Method
    | AddCallEdge of callForm:codeLocation * callTo: codeLocation
    | GetShortestDistancesToGoals
        of AsyncReplyChannel<ResizeArray<codeLocation * codeLocation * int>> * array<codeLocation>
    | GetReachableGoals
        of AsyncReplyChannel<Dictionary<codeLocation,HashSet<codeLocation>>> * array<codeLocation>
    | GetDistanceToNearestGoal
        of AsyncReplyChannel<seq<IGraphTrackableState * int>> * seq<IGraphTrackableState>

type ApplicationGraph() as this =        
    //let mutable firstFreeVertexId = 0<inputGraphVertex>
    //let methodToFirstVertexIdMapping = Dictionary<Method,int<inputGraphVertex>>()    
    //let stateToStartVertex = Dictionary<IGraphTrackableState, StartVertex>()
    //let startVertexToStates = Dictionary<StartVertex, HashSet<IGraphTrackableState>>()
    //let cfgs = Dictionary<MethodBase, CfgInfo>()
    //let innerGraphVerticesToCodeLocationMap = ResizeArray<_>()
    //let existingCalls = HashSet<codeLocation*codeLocation>()
    //let mutable queryEngine = GraphQueryEngine()
    //let codeLocationToVertex = Dictionary<codeLocation, int<inputGraphVertex>>()        
    //let getVertexByCodeLocation (pos:codeLocation) = Unchecked.defaultof<_>
            //codeLocationToVertex.[{pos with offset = pos.method.CFG.ResolveBasicBlock pos.offset}]
        
    let toDot filePath = ()
    (*
        let clusters = 
            seq{
                for method in methodToFirstVertexIdMapping.Keys do
                    let clusterName = method.Name
                    let vertices =                     
                        method.CFG.SortedOffsets
                        |> Seq.map (fun vertex -> getVertexByCodeLocation {method = method; offset = vertex})
                    yield Cluster(clusterName, vertices)
                }
        *)
        //queryEngine.ToDot(clusters, filePath)
                
    let registerMethod (method:Method) =
        if not method.HasBody
        then Logger.trace "Attempt to register method without body."
        (*
        if not <| methodToFirstVertexIdMapping.ContainsKey method
        then
            method.CFG.SortedOffsets
            |> ResizeArray.iter (fun offset ->
                let vertex = firstFreeVertexId
                let codeLocation = {method = method; offset = offset}
                codeLocationToVertex.Add(codeLocation, vertex)
                innerGraphVerticesToCodeLocationMap.Add codeLocation
                firstFreeVertexId <- firstFreeVertexId + 1<inputGraphVertex>)
            for kvp in method.CFG.Edges do
                let srcVertex = codeLocationToVertex.[{method = method; offset = kvp.Key}]
                for targetOffset in kvp.Value do
                    let targetVertex = codeLocationToVertex.[{method = method; offset = targetOffset}]
                    queryEngine.AddCfgEdge <| Edge (srcVertex, targetVertex)        
                
            methodToFirstVertexIdMapping.Add(method, firstFreeVertexId)        
          *)     
    let addCallEdge (callSource:codeLocation) (callTarget:codeLocation) =   
        let callerMethodCfgInfo = callSource.method.CFG //cfgs.[callSource.method]
        let calledMethodCfgInfo = callTarget.method.CFG // cfgs.[callTarget.method]
        //let callFrom = getVertexByCodeLocation callSource
        //let callTo = getVertexByCodeLocation callTarget                    
        ()
        (*
        if not <| existingCalls.Contains (callSource, callTarget)
        then
            let added = existingCalls.Add(callSource,callTarget)
            assert added             
            let returnTo =
                if callTarget.method.IsStaticConstructor
                then callFrom
                else
                    let exists, location = callerMethodCfgInfo.Calls.TryGetValue callSource.offset
                    if exists
                    then
                        let returnTo = getVertexByCodeLocation {callSource with offset = location.ReturnTo}
                        queryEngine.RemoveCfgEdge (Edge (callFrom, returnTo))
                        returnTo
                    else getVertexByCodeLocation {callSource with offset = callerMethodCfgInfo.Sinks.[0]}
            let callEdge = Edge(callFrom, callTo) |> if callTarget.method.IsStaticConstructor then Virtual else Real
            let returnEdges =
                calledMethodCfgInfo.Sinks
                |> Array.map(fun sink -> getVertexByCodeLocation {callTarget with offset = sink})
                |> Array.map (fun returnFrom -> Edge(returnFrom, returnTo))
            queryEngine.AddCallReturnEdges (callEdge, returnEdges)
            //toDot "cfg_debug.dot"
    *)
        
    let moveState (initialPosition: codeLocation) (stateWithNewPosition: IGraphTrackableState) =
        ()
        (*
        let initialVertexInInnerGraph = getVertexByCodeLocation initialPosition            
        let finalVertexInnerGraph = getVertexByCodeLocation stateWithNewPosition.CodeLocation 
        if initialVertexInInnerGraph <> finalVertexInnerGraph
        then            
            let previousStartVertex = stateToStartVertex.[stateWithNewPosition]
            let historySpecificRSMState =
                if existingCalls.Contains (initialPosition, stateWithNewPosition.CodeLocation)
                then
                    Edge (getVertexByCodeLocation initialPosition, getVertexByCodeLocation stateWithNewPosition.CodeLocation)
                    |> queryEngine.GetTerminalForCallEdge
                    |> fun x -> queryEngine.AddHistoryStep(previousStartVertex, x)                        
                elif Array.contains initialPosition.offset initialPosition.method.CFG.Sinks
                then queryEngine.PopHistoryStep previousStartVertex                   
                else previousStartVertex.HistorySpecificRSMState            
            let startVertex = StartVertex(getVertexByCodeLocation stateWithNewPosition.CodeLocation, historySpecificRSMState)
            let exists, states = startVertexToStates.TryGetValue startVertex
            if exists
            then
                let added = states.Add stateWithNewPosition                
                assert added
            else startVertexToStates.Add(startVertex, HashSet<_>[|stateWithNewPosition|])
            stateToStartVertex.[stateWithNewPosition] <- startVertex
            let removed = startVertexToStates.[previousStartVertex].Remove stateWithNewPosition
            assert removed
            queryEngine.AddStartVertex startVertex
            if startVertexToStates.[previousStartVertex].Count = 0
            then queryEngine.RemoveStartVertex previousStartVertex
            *)
            
    let addStates (parentState:Option<IGraphTrackableState>) (states:array<IGraphTrackableState>) =
        ()
        (*
        let history =
            match parentState with
            | None -> None
            | Some state -> stateToStartVertex.[state].HistorySpecificRSMState
                
        let startVertices =
            states
            |> Array.map (fun state ->
                let startVertex = StartVertex (getVertexByCodeLocation state.CodeLocation, history)
                stateToStartVertex.Add(state, startVertex)
                let exists, states = startVertexToStates.TryGetValue startVertex
                if exists
                then
                    let added = states.Add state
                    assert added
                else startVertexToStates.Add(startVertex, HashSet<_>[|state|])                    
                startVertex)
            
        queryEngine.AddStartVertices startVertices
        *)
    
    let getShortestDistancesToGoals (states:array<codeLocation>) = 
        states
        |> Array.choose (fun state -> None)
            //let exists, distances = knownDistances.TryGetValue (codeLocationToVertex state)
            //if exists then Some distances else None)
        |> ResizeArray.concat

    let messagesProcessor = MailboxProcessor.Start(fun inbox ->       
        async{            
            while true do
                let! message = inbox.Receive()
                try                    
                    match message with
                    | ResetQueryEngine ->
                        Logger.trace "Application graph reset."
                        //queryEngine <- GraphQueryEngine ()
                        //innerGraphVerticesToCodeLocationMap.Clear()
                        //firstFreeVertexId <- 0<inputGraphVertex>
                        //methodToFirstVertexIdMapping.Clear()
                        //stateToStartVertex.Clear()
                        //startVertexToStates.Clear()                        
                        //existingCalls.Clear()
                        //codeLocationToVertex.Clear()
                    | RegisterMethod method ->
                        //Logger.trace "1"
                        registerMethod method
                    | AddCallEdge (_from, _to) ->
                        //Logger.trace "2"
                        //registerMethod _from.method 
                        //registerMethod _to.method                        
                        addCallEdge _from _to
                        //toDot "cfg.dot"
                    | AddGoals positions ->
                        //Logger.trace "3"
                        //positions
                        //|> Array.map getVertexByCodeLocation 
                        //|> queryEngine.AddFinalVertices
                        () 
                    | RemoveGoal pos ->
                        //Logger.trace "4"
                        //getVertexByCodeLocation pos
                        //|> queryEngine.RemoveFinalVertex
                        ()
                    | SpawnStates states ->
                        //Logger.trace "5"
                        Array.ofSeq states |> addStates None
                        
                    | AddForkedStates (parentState, forkedStates) ->
                        //Logger.trace "6"
                        addStates (Some parentState) (Array.ofSeq forkedStates)
                    | MoveState (_from,_to) ->
                        //Logger.trace $"Moved: %A{getVertexByCodeLocation _from} -> %A{getVertexByCodeLocation _to.CodeLocation}"                            
                        moveState _from _to
                    | GetShortestDistancesToGoals (replyChannel, states) ->
                        //Logger.trace "7"
                        replyChannel.Reply (getShortestDistancesToGoals states)
                    | GetDistanceToNearestGoal (replyChannel, states) ->
                        //Logger.trace "8"
                        let result = Unchecked.defaultof<_>
                            (*
                            states
                            |> Seq.choose (fun state ->
                                match queryEngine.GetDistanceToNearestGoal stateToStartVertex.[state] with
                                | Some (_,distance) -> Some (state, int distance)
                                | None -> None)*)
                        replyChannel.Reply result
                    | GetReachableGoals (replyChannel, states) -> replyChannel.Reply (Dictionary<_,_>())
                with
                | e ->
                    Logger.error $"Something wrong in application graph messages processor: \n %A{e} \n %s{e.Message} \n %s{e.StackTrace}"
                    //match message with
                    //| AddCFG (Some ch, _) -> ch.Reply (Unchecked.defaultof<CfgInfo>)
                    //| _ -> ()
        }            
    )
  
    do
        messagesProcessor.Error.Add(fun e ->
            Logger.error $"Something wrong in application graph messages processor: \n %A{e} \n %s{e.Message} \n %s{e.StackTrace}"
            raise e
            )

    member this.RegisterMethod (method: Method) =
        //if method.HasBody 
        messagesProcessor.Post (RegisterMethod method)

    member this.AddCallEdge (sourceLocation : codeLocation) (targetLocation : codeLocation) =
        messagesProcessor.Post <| AddCallEdge (sourceLocation, targetLocation)

    member this.SpawnState (state:IGraphTrackableState) =
        messagesProcessor.Post <| SpawnStates [|state|]

    member this.SpawnStates (states:seq<IGraphTrackableState>) =
        messagesProcessor.Post <| SpawnStates states

    member this.AddForkedStates (parentState:IGraphTrackableState) (states:seq<IGraphTrackableState>) =
        messagesProcessor.Post <| AddForkedStates (parentState,states)
        //addStates (Some parentState) (Array.ofSeq states)
        
    member this.MoveState (fromLocation : codeLocation) (toLocation : IGraphTrackableState) =               
        messagesProcessor.Post <| MoveState (fromLocation, toLocation)      
        //tryGetCfgInfo toLocation.CodeLocation.method |> ignore                            
        //moveState fromLocation toLocation
        
    member x.AddGoal (location:codeLocation) =
        messagesProcessor.Post <| AddGoals [|location|]

    member x.AddGoals (locations:array<codeLocation>) =
        messagesProcessor.Post <| AddGoals locations

    member x.RemoveGoal (location:codeLocation) =
        messagesProcessor.Post <| RemoveGoal location

    member this.GetShortestDistancesToAllGoalsFromStates (states: array<codeLocation>) =
        messagesProcessor.PostAndReply (fun ch -> GetShortestDistancesToGoals(ch, states))

    member this.GetDistanceToNearestGoal (states: seq<IGraphTrackableState>) =
        messagesProcessor.PostAndReply (fun ch -> GetDistanceToNearestGoal(ch, states))

    member this.GetGoalsReachableFromStates (states: array<codeLocation>) =
        messagesProcessor.PostAndReply (fun ch -> GetReachableGoals(ch, states))

    member this.ResetQueryEngine() =
        messagesProcessor.Post ResetQueryEngine

type IVisualizer =
    abstract AddState : IGraphTrackableState -> unit
    abstract TerminateState : IGraphTrackableState -> unit
    abstract VisualizeGraph : unit -> unit
    abstract VisualizeStep : codeLocation -> IGraphTrackableState -> IGraphTrackableState seq -> unit

type NullVisualizer() =
    interface IVisualizer with
        override x.AddState _ = ()
        override x.TerminateState _ = ()
        override x.VisualizeGraph () = ()
        override x.VisualizeStep _ _ _ = ()

module Application =
    let private methods = Dictionary<MethodBase, Method>()
    let private _loadedMethods = HashSet<_>()
    let loadedMethods = _loadedMethods :> seq<_>
    let graph = ApplicationGraph()
    let mutable visualizer : IVisualizer = NullVisualizer()

    let getMethod (m : MethodBase) : Method =        
        let method = Dict.getValueOrUpdate methods m (fun () -> Method(m))
        if method.HasBody then graph.RegisterMethod method
        method

    let setVisualizer (v : IVisualizer) =
        visualizer <- v

    let spawnStates states =
        graph.SpawnStates states
        states |> Seq.iter (fun state -> visualizer.AddState state)
        visualizer.VisualizeGraph()

    let moveState fromLoc toState forked =
        graph.MoveState fromLoc toState
        graph.AddForkedStates toState forked
        //let d = graph.GetDistanceToNearestGoal (seq {yield toState; yield! forked})
        //Logger.trace $"Distances: %A{d |> Seq.map snd}"
        visualizer.VisualizeStep fromLoc toState forked

    let terminateState state =
        // TODO: gsv: propagate this into application graph
        visualizer.TerminateState state

    let addCallEdge = graph.AddCallEdge
    let addGoal = graph.AddGoal
    let addGoals = graph.AddGoals
    let removeGoal = graph.RemoveGoal

    do
        MethodWithBody.InstantiateNew <- fun m -> getMethod m :> MethodWithBody
        Method.ReportCFGLoaded <- fun m ->
            //graph.RegisterMethod m
            let added = _loadedMethods.Add(m) in assert added
