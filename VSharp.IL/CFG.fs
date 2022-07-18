namespace VSharp

open System.Reflection
open System.Collections.Generic

open CFPQ_GLL
open CFPQ_GLL.GLL
open CFPQ_GLL.GSS
open CFPQ_GLL.InputGraph
open CFPQ_GLL.RSM
open CFPQ_GLL.SPPF
open FSharpx.Collections
open VSharp
open VSharp.Core

type IGraphTrackableState =
    abstract member CodeLocation: codeLocation
    abstract member CallStack: list<codeLocation*codeLocation>

[<Struct>]
type CallInfo =
    val CallFrom: offset
    val ReturnTo: offset
    val IsExternalStaticCall: bool
    new (callFrom, returnTo) =
        {
            CallFrom = callFrom
            ReturnTo = returnTo
            IsExternalStaticCall = false
        }
    new (callFrom, returnTo, isExternalStatic) =
        {
            CallFrom = callFrom
            ReturnTo = returnTo
            IsExternalStaticCall = isExternalStatic
        }

type private BasicBlock (startVertex: offset) =
    let innerVertices = ResizeArray<offset>()
    let mutable finalVertex = None 
    member this.StartVertex = startVertex
    member this.InnerVertices with get () = innerVertices
    member this.AddVertex v = innerVertices.Add v
    member this.FinalVertex
        with get () =
                match finalVertex with
                | Some v -> v
                | None -> failwith "Final vertex of this basic block is not specified yet."
        and set v = finalVertex <- Some v

type CfgTemporaryData (methodBase : MethodBase) =
    let ilBytes = Instruction.getILBytes methodBase
    let exceptionHandlers = Instruction.getEHSBytes methodBase
    let sortedOffsets = ResizeArray<offset>()
    let edges = Dictionary<offset, HashSet<offset>>()
    let sinks = ResizeArray<_>()
    let calls = ResizeArray<CallInfo>()
    let loopEntries = HashSet<offset>()   
    
    let dfs (startVertices : array<offset>) =
        let used = HashSet<offset>()        
        let verticesOffsets = HashSet<offset> startVertices
        let addVertex v = verticesOffsets.Add v |> ignore        
        let greyVertices = HashSet<offset>()
        let vertexToBasicBloc: array<Option<BasicBlock>> = Array.init ilBytes.Length (fun _ -> None)
        
        let splitEdge edgeStart edgeFinal intermediatePoint =
            let isRemoved = edges.[edgeStart].Remove edgeFinal
            assert isRemoved
            let isAdded = edges.[edgeStart].Add intermediatePoint
            assert isAdded
            edges.Add(intermediatePoint, HashSet<_>[|edgeFinal|])
            
        let splitBasicBlock (block:BasicBlock) intermediatePoint =
            let newBlock = BasicBlock(intermediatePoint)
            newBlock.FinalVertex <- block.FinalVertex
            let tmp = ResizeArray block.InnerVertices
            for v in tmp do
                if v > intermediatePoint
                then
                    let isRemoved = block.InnerVertices.Remove v
                    assert isRemoved
                    newBlock.AddVertex v
                    vertexToBasicBloc.[v] <- Some newBlock
            block.FinalVertex <- intermediatePoint
            let isRemoved = block.InnerVertices.Remove intermediatePoint
            assert isRemoved

        let addEdge src dst =
            addVertex src
            addVertex dst
            if src <> dst
            then
                let exists,outgoingEdges = edges.TryGetValue src
                if exists
                then outgoingEdges.Add dst |> ignore
                else edges.Add(src, HashSet [|dst|])
                match vertexToBasicBloc.[dst] with
                | None -> ()
                | Some block ->
                    if block.InnerVertices.Contains dst && block.FinalVertex <> dst 
                    then
                        splitEdge block.StartVertex block.FinalVertex dst
                        splitBasicBlock block dst
                                        
            
        let rec dfs' (currentBasicBlock : BasicBlock) (currentVertex : offset) =
            
            vertexToBasicBloc.[currentVertex] <- Some currentBasicBlock
            
            if used.Contains currentVertex
            then
                currentBasicBlock.FinalVertex <- currentVertex
                addEdge currentBasicBlock.StartVertex currentVertex
                if greyVertices.Contains currentVertex
                then loopEntries.Add currentVertex |> ignore
            else 
                greyVertices.Add currentVertex |> ignore
                used.Add currentVertex |> ignore
                let opCode = Instruction.parseInstruction methodBase currentVertex                

                let dealWithJump src dst =
                    addVertex src
                    addVertex dst 
                    addEdge src dst
                    dfs' (BasicBlock dst)  dst
                
                let processCall callFrom returnTo isStaticCall =
                    calls.Add(CallInfo(callFrom,returnTo,isStaticCall))
                    currentBasicBlock.FinalVertex <- currentVertex
                    addEdge currentBasicBlock.StartVertex currentVertex
                    if isStaticCall
                    then addEdge callFrom returnTo
                    dfs' (BasicBlock returnTo) returnTo
                
                let ipTransition = Instruction.findNextInstructionOffsetAndEdges opCode ilBytes currentVertex

                match ipTransition with
                | FallThrough offset when Instruction.isDemandingCallOpCode opCode ->
                    let calledMethod = TokenResolver.resolveMethodFromMetadata methodBase ilBytes (currentVertex + opCode.Size)
                    if not <| Reflection.isExternalMethod calledMethod
                    then processCall currentVertex offset true
                    //elif calledMethod.IsStatic 
                    //then processCall currentVertex offset true
                    else
                        currentBasicBlock.AddVertex offset
                        dfs' currentBasicBlock offset
                | FallThrough offset ->                    
                    currentBasicBlock.AddVertex offset
                    dfs' currentBasicBlock offset
                | ExceptionMechanism ->
                    //TODO gsv fix it.
                    currentBasicBlock.FinalVertex <- currentVertex
                    addEdge currentBasicBlock.StartVertex currentVertex
                    calls.Add(CallInfo(currentVertex,currentVertex+1))
                | Return ->
                    addVertex currentVertex
                    sinks.Add currentVertex
                    currentBasicBlock.FinalVertex <- currentVertex
                    addEdge currentBasicBlock.StartVertex currentVertex
                | UnconditionalBranch target ->
                    currentBasicBlock.FinalVertex <- currentVertex
                    addEdge currentBasicBlock.StartVertex currentVertex
                    dealWithJump currentVertex target
                | ConditionalBranch (fallThrough, offsets) ->
                    currentBasicBlock.FinalVertex <- currentVertex
                    addEdge currentBasicBlock.StartVertex currentVertex
                    dealWithJump currentVertex fallThrough
                    offsets |> List.iter (dealWithJump currentVertex)
                
                greyVertices.Remove currentVertex |> ignore
        
        startVertices
        |> Array.iter (fun v -> dfs' (BasicBlock v) v)
        
        verticesOffsets
        |> Seq.sort
        |> Seq.iter sortedOffsets.Add
        
    do
        let startVertices =
            [|
             yield 0
             for handler in exceptionHandlers do
                 yield handler.handlerOffset
                 match handler.ehcType with
                 | Filter offset -> yield offset
                 | _ -> ()
            |]
        
        dfs startVertices
        
    member this.MethodBase = methodBase
    member this.ILBytes = ilBytes
    member this.SortedOffsets = sortedOffsets
    member this.Edges = edges
    member this.Calls = calls
    member this.Sinks = sinks.ToArray()
    member this.LoopEntries = loopEntries

type CfgInfo (cfg:CfgTemporaryData) =
    let resolveBasicBlock offset =
        let rec binSearch (sortedOffsets : List<offset>) offset l r =
            if l >= r then sortedOffsets.[l]
            else
                let mid = (l + r) / 2
                let midValue = sortedOffsets.[mid]
                if midValue = offset
                then midValue
                elif midValue < offset
                then binSearch sortedOffsets offset (mid + 1) r
                else binSearch sortedOffsets offset l (mid - 1)
    
        binSearch cfg.SortedOffsets offset 0 (cfg.SortedOffsets.Count - 1)
    
    let sinks = cfg.Sinks |> Array.map resolveBasicBlock
    let loopEntries = cfg.LoopEntries   
    let calls =
        let res = Dictionary<_,_>()
        cfg.Calls
        |> ResizeArray.iter (fun callInfo -> res.Add(callInfo.CallFrom, callInfo))
        res
    
    member this.MethodBase = cfg.MethodBase
    member this.IlBytes = cfg.ILBytes
    member this.SortedOffsets = cfg.SortedOffsets
    member this.Sinks = sinks 
    member this.Calls = calls
    member this.IsLoopEntry offset = loopEntries.Contains offset
    member this.ResolveBasicBlock offset =
        resolveBasicBlock offset

type private ApplicationGraphMessage =
    | AddGoals of array<codeLocation>
    | RemoveGoal of codeLocation
    | AddStates of seq<IGraphTrackableState>
    | AddForkedStates of parentState:IGraphTrackableState * forkedStates:seq<IGraphTrackableState>
    | MoveState of positionForm:codeLocation * positionTo: IGraphTrackableState
    | AddCFG of Option<AsyncReplyChannel<CfgInfo>> *  MethodBase
    | AddCallEdge of callForm:codeLocation * callTo: codeLocation
    | GetShortestDistancesToGoals
        of AsyncReplyChannel<ResizeArray<codeLocation * codeLocation * int>> * array<codeLocation>
    | GetReachableGoals
        of AsyncReplyChannel<Dictionary<codeLocation,HashSet<codeLocation>>> * array<codeLocation>
    | GetDistanceToNearestGoal
        of AsyncReplyChannel<seq<IGraphTrackableState * int>> * seq<IGraphTrackableState>
      
type ApplicationGraph() as this =        
    let mutable firstFreeVertexId = 0<inputGraphVertex>
    let cfgToFirstVertexIdMapping = Dictionary<MethodBase,int<inputGraphVertex>>()    
    let goalsInInnerGraph = ResizeArray<_>()
    let stateToStartVertex = Dictionary<IGraphTrackableState, StartVertex>()
    let startVertexToStates = Dictionary<StartVertex, HashSet<IGraphTrackableState>>()
    let cfgs = Dictionary<MethodBase, CfgInfo>()    
    let innerGraphVerticesToCodeLocationMap = ResizeArray<_>() //SortedDictionary<_,_>(comparer = RangesComparer())
    let existingCalls = HashSet<codeLocation*codeLocation>()
    let queryEngine = GraphQueryEngine()
    let codeLocationToVertex = Dictionary<codeLocation, int<inputGraphVertex>>()        
    let getVertexByCodeLocation (pos:codeLocation) =
            codeLocationToVertex.[{pos with offset = cfgs.[pos.method].ResolveBasicBlock pos.offset}]
        
    let toDot filePath =
        let clusters = 
            seq{
                for kvp in cfgs do
                    let clusterName = kvp.Value.MethodBase.Name
                    let vertices =                     
                        kvp.Value.SortedOffsets
                        |> Seq.map (fun vertex -> getVertexByCodeLocation  {method = kvp.Value.MethodBase; offset = vertex})
                    yield Cluster(clusterName, vertices)
                }
    
        queryEngine.ToDot(clusters, filePath)
                
    let buildCFG (methodBase:MethodBase) =
        Logger.trace $"Add CFG for %A{methodBase.Name}."
        let cfg = CfgTemporaryData(methodBase)
        cfg.SortedOffsets
        |> ResizeArray.iter (fun offset ->
            let vertex = firstFreeVertexId
            let codeLocation = {method = methodBase; offset = offset}
            codeLocationToVertex.Add(codeLocation, vertex)
            innerGraphVerticesToCodeLocationMap.Add codeLocation
            firstFreeVertexId <- firstFreeVertexId + 1<inputGraphVertex>)
        for kvp in cfg.Edges do
            let srcVertex = codeLocationToVertex.[{method = methodBase; offset = kvp.Key}]
            for targetOffset in kvp.Value do
                let targetVertex = codeLocationToVertex.[{method = methodBase; offset = targetOffset}]
                queryEngine.AddCfgEdge <| Edge (srcVertex, targetVertex)        
            
        cfgToFirstVertexIdMapping.Add(methodBase, firstFreeVertexId)
        cfg            
        
    let getCodeLocation (vertex:int<inputGraphVertex>) =
        let codeLocation = innerGraphVerticesToCodeLocationMap.[int vertex]
        codeLocation
               
    let addCallEdge (callSource:codeLocation) (callTarget:codeLocation) =   
        let callerMethodCfgInfo = cfgs.[callSource.method]
        let calledMethodCfgInfo = cfgs.[callTarget.method]
        let callFrom = getVertexByCodeLocation callSource
        let callTo = getVertexByCodeLocation callTarget                    

        if not <| existingCalls.Contains (callSource, callTarget)
        then
            let added = existingCalls.Add(callSource,callTarget)
            assert added
            let returnTo =
                if Reflection.isStaticConstructor callTarget.method
                then callFrom
                else
                    let exists, location = callerMethodCfgInfo.Calls.TryGetValue callSource.offset
                    if exists
                    then
                        let returnTo = getVertexByCodeLocation {callSource with offset = location.ReturnTo}
                        queryEngine.RemoveCfgEdge (Edge (callFrom, returnTo))
                        returnTo
                    else getVertexByCodeLocation {callSource with offset = callerMethodCfgInfo.Sinks.[0]}
            let callEdge = Edge(callFrom, callTo)
            let returnEdges =
                calledMethodCfgInfo.Sinks
                |> Array.map(fun sink -> getVertexByCodeLocation {callTarget with offset = sink})
                |> Array.map (fun returnFrom -> Edge(returnFrom, returnTo))
            queryEngine.AddCallReturnEdges (callEdge, returnEdges)            
        
    let moveState (initialPosition: codeLocation) (stateWithNewPosition: IGraphTrackableState) =        
        let initialVertexInInnerGraph = getVertexByCodeLocation initialPosition            
        let finalVertexInnerGraph = getVertexByCodeLocation stateWithNewPosition.CodeLocation 
        if initialVertexInInnerGraph <> finalVertexInnerGraph
        then            
            let previousStartVertex = stateToStartVertex.[stateWithNewPosition]
            let history =
                if existingCalls.Contains (initialPosition, stateWithNewPosition.CodeLocation)
                then
                    Edge (getVertexByCodeLocation initialPosition, getVertexByCodeLocation stateWithNewPosition.CodeLocation)
                    |> queryEngine.GetTerminalForCallEdge
                    |> fun x -> x :: previousStartVertex.CallHistory
                elif Array.contains initialPosition.offset cfgs.[initialPosition.method].Sinks//   <> stateWithNewPosition.CodeLocation.method
                then List.tail previousStartVertex.CallHistory 
                else previousStartVertex.CallHistory
            Logger.trace $"History length: %A{history.Length}."
            let startVertex = StartVertex(getVertexByCodeLocation stateWithNewPosition.CodeLocation, history)
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
            
    let addStates (parentState:Option<IGraphTrackableState>) (states:array<IGraphTrackableState>) =
        let history =
            match parentState with
            | None -> []
            | Some state -> stateToStartVertex.[state].CallHistory
                
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
    
    let getShortestDistancesToGoals (states:array<codeLocation>) = 
        states
        |> Array.choose (fun state -> None)
            //let exists, distances = knownDistances.TryGetValue (codeLocationToVertex state)
            //if exists then Some distances else None)
        |> ResizeArray.concat
            
    let messagesProcessor = MailboxProcessor.Start(fun inbox ->
        let tryGetCfgInfo methodBase =
            let exists,cfgInfo = cfgs.TryGetValue methodBase  
            if not exists
            then
                let cfg = buildCFG methodBase
                let cfgInfo = CfgInfo cfg
                cfgs.Add(methodBase, cfgInfo)
                queryEngine.AddVertices (cfg.SortedOffsets |> ResizeArray.map (fun offset -> getVertexByCodeLocation {offset = offset; method = methodBase}))
                cfgInfo
            else cfgInfo
            
        async{            
            while true do
                let! message = inbox.Receive()
                try                    
                    match message with
                    | AddCFG (replyChannel, methodBase) ->
                        let reply cfgInfo =
                            match replyChannel with
                            | Some ch -> ch.Reply cfgInfo
                            | None -> ()
                        let cfgInfo = tryGetCfgInfo methodBase                    
                        reply cfgInfo                        
                            
                    | AddCallEdge (_from, _to) ->
                        tryGetCfgInfo _from.method |> ignore
                        tryGetCfgInfo _to.method |> ignore                       
                        addCallEdge _from _to
                        //toDot "cfg.dot"
                    | AddGoals positions ->
                        positions
                        |> Array.map getVertexByCodeLocation 
                        |> queryEngine.AddFinalVertices 
                    | RemoveGoal pos ->
                        getVertexByCodeLocation pos
                        |> queryEngine.RemoveFinalVertex
                    | AddStates states -> Array.ofSeq states |> addStates None
                    | AddForkedStates (parentState, forkedStates) ->
                        addStates (Some parentState) (Array.ofSeq forkedStates)
                    | MoveState (_from,_to) ->
                        tryGetCfgInfo _to.CodeLocation.method |> ignore                            
                        moveState _from _to
                    | GetShortestDistancesToGoals (replyChannel, states) ->
                        replyChannel.Reply (getShortestDistancesToGoals states)
                    | GetDistanceToNearestGoal (replyChannel, states) ->
                        let result =
                            states
                            |> Seq.choose (fun state ->
                                match queryEngine.GetDistanceToNearestGoal stateToStartVertex.[state] with
                                | Some (_,distance) -> Some (state, int distance)
                                | None -> None)
                        replyChannel.Reply result
                    | GetReachableGoals (replyChannel, states) -> replyChannel.Reply (Dictionary<_,_>())
                with
                | e ->
                    Logger.error $"Something wrong in application graph messages processor: \n %A{e} \n %s{e.Message} \n %s{e.StackTrace}"
                    match message with
                    | AddCFG (Some ch, _) -> ch.Reply (Unchecked.defaultof<CfgInfo>)
                    | _ -> ()
        }            
    )
  
    do
        messagesProcessor.Error.Add(fun e ->
            Logger.error $"Something wrong in application graph messages processor: \n %A{e} \n %s{e.Message} \n %s{e.StackTrace}"
            raise e
            )

    member this.GetCfg (methodBase: MethodBase) =        
         messagesProcessor.PostAndReply (fun ch -> AddCFG (Some ch, methodBase))
            
    member this.RegisterMethod (methodBase: MethodBase) =            
        messagesProcessor.Post (AddCFG (None, methodBase))        
        
    member this.AddCallEdge (sourceLocation : codeLocation) (targetLocation : codeLocation) =        
        messagesProcessor.Post <| AddCallEdge (sourceLocation, targetLocation)
        
    member this.AddState (state:IGraphTrackableState) =            
        messagesProcessor.Post <| AddStates [|state|]
        
    member this.AddStates (states:seq<IGraphTrackableState>) =            
        messagesProcessor.Post <| AddStates states
        
    member this.AddForkedStates (parentState:IGraphTrackableState, states:seq<IGraphTrackableState>) =            
        messagesProcessor.Post <| AddForkedStates (parentState,states)
        
    member this.MoveState (fromLocation : codeLocation) (toLocation : IGraphTrackableState) =
        messagesProcessor.Post <| MoveState (fromLocation, toLocation)
        
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
module CFG =
    let applicationGraph = ApplicationGraph()