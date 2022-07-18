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
open VSharp.Concolic
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
                    //currentBasicBlock.FinalVertex <- currentVertex
                    //addEdge currentBasicBlock.StartVertex currentVertex
                    //dealWithJump currentVertex target
                    currentBasicBlock.AddVertex target
                    dfs' currentBasicBlock target
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
    let resolveBasicBlockIndex offset =
        let rec binSearch (sortedOffsets : List<offset>) offset l r =
            if l >= r then l
            else
                let mid = (l + r) / 2
                let midValue = sortedOffsets.[mid]
                let leftIsLefter = midValue <= offset
                let rightIsRighter = mid + 1 >= sortedOffsets.Count || sortedOffsets.[mid + 1] > offset
                if leftIsLefter && rightIsRighter then mid
                elif not rightIsRighter
                    then binSearch sortedOffsets offset (mid + 1) r
                    else binSearch sortedOffsets offset l (mid - 1)

        binSearch cfg.SortedOffsets offset 0 (cfg.SortedOffsets.Count - 1)

    let resolveBasicBlock offset = cfg.SortedOffsets.[resolveBasicBlockIndex offset]

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
    member this.Edges = cfg.Edges
    member this.Sinks = sinks
    member this.Calls = calls
    member this.IsLoopEntry offset = loopEntries.Contains offset
    member this.ResolveBasicBlock offset = resolveBasicBlock offset

    // Returns a sequence of strings, one per instruction in basic block
    member this.BasicBlockToString (offset : offset) : string seq =
        let idx = resolveBasicBlockIndex offset
        let offset = cfg.SortedOffsets.[idx]
        let parsedInstrs = Instruction.getParsedIL cfg.MethodBase
        let mutable instr = parsedInstrs |> Array.find (fun instr -> int instr.offset = offset)
        let endInstr =
            if idx + 1 < cfg.SortedOffsets.Count then
                let nextBBOffset = cfg.SortedOffsets.[idx + 1]
                parsedInstrs |> Array.find (fun instr -> int instr.offset = nextBBOffset)
            else parsedInstrs.[parsedInstrs.Length - 1].next
        seq {
            while not <| LanguagePrimitives.PhysicalEquality instr endInstr do
                yield ILRewriter.PrintILInstr None None cfg.MethodBase instr
                instr <- instr.next
        }



type private ApplicationGraphMessage =
    | AddGoals of array<codeLocation>
    | RemoveGoal of codeLocation
    | AddStates of seq<IGraphTrackableState>
    | MoveState of positionFrom: codeLocation * positionTo: IGraphTrackableState * forks: IGraphTrackableState seq
    | AddCFG of Option<AsyncReplyChannel<CfgInfo>> *  MethodBase
    | AddCallEdge of callForm:codeLocation * callTo: codeLocation
    | GetShortestDistancesToGoals
        of AsyncReplyChannel<ResizeArray<codeLocation * codeLocation * int>> * array<codeLocation>
    | GetReachableGoals
        of AsyncReplyChannel<Dictionary<codeLocation,HashSet<codeLocation>>> * array<codeLocation>
    | GetDistanceToNearestGoal
        of AsyncReplyChannel<seq<IGraphTrackableState * int>> * seq<IGraphTrackableState>

type private RangesComparer() =
    interface IComparer<int<inputGraphVertex>*int<inputGraphVertex>> with
        member this.Compare ((x1,x2),(y1,y2)) =
            if (x1 <= y1 && x2 >= y2) || (y1 <= x1 && y2 >= x2)
            then 0
            elif x2 < y1
            then -1
            elif y2 < x1
            then 1
            else failwithf $"You can rty try to compare incomparable ranges: (%A{x1},%A{x2}) and (%A{y1},%A{y2})"

type IVisualizer =
    abstract AddMarker : codeLocation -> unit
    abstract VisualizeGraph : unit -> unit
    abstract VisualizeStep : codeLocation -> codeLocation -> codeLocation seq -> unit

type NullVisualizer() =
    interface IVisualizer with
        override x.AddMarker _ = ()
        override x.VisualizeGraph () = ()
        override x.VisualizeStep _ _ _ = ()

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
    let resolveCodeLocation (pos : codeLocation) =
        {pos with offset = cfgs.[pos.method].ResolveBasicBlock pos.offset}
    let getVertexByCodeLocation (pos : codeLocation) =
        codeLocationToVertex.[resolveCodeLocation pos]

    let mutable visualizer : IVisualizer = NullVisualizer()

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
        //let nextFreeVertexIndex = firstFreeVertexId + cfg.ILBytes.Length * 1<inputGraphVertex>
        //innerGraphVerticesToCodeLocationMap.Add((firstFreeVertexId, nextFreeVertexIndex - 1<inputGraphVertex>),(firstFreeVertexId, methodBase))
        //firstFreeVertexId <- nextFreeVertexIndex
        
        cfg            
        
    let getCodeLocation (vertex:int<inputGraphVertex>) =
        let codeLocation = innerGraphVerticesToCodeLocationMap.[int vertex]
        //{method = method; offset = int (vertex - firstVertexId)}
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
                        //queryEngine.RemoveCfgEdge (Edge (callFrom, returnTo))
                        returnTo
                    else getVertexByCodeLocation {callSource with offset = callerMethodCfgInfo.Sinks.[0]}
            let callEdge = Edge(callFrom, callTo)
            let returnEdges =
                calledMethodCfgInfo.Sinks
                |> Array.map(fun sink -> getVertexByCodeLocation {callTarget with offset = sink})
                |> Array.map (fun returnFrom -> Edge(returnFrom, returnTo))
            queryEngine.AddCallReturnEdges (callEdge, returnEdges)            

    let addStartVertex (state : IGraphTrackableState) =
        let resolvedLocation = resolveCodeLocation state.CodeLocation
        let startVertex = StartVertex (codeLocationToVertex.[resolvedLocation], [])
        if not <| stateToStartVertex.ContainsKey state then
            stateToStartVertex.Add(state, startVertex)
        let exists, states = startVertexToStates.TryGetValue startVertex
        if exists
        then
            let added = states.Add state
            assert added
        else startVertexToStates.Add(startVertex, HashSet<_>[|state|])
        startVertex, resolvedLocation

    let moveState (initialPosition: codeLocation) (stateWithNewPosition: IGraphTrackableState) (forks: IGraphTrackableState seq) =
        let resolvedInitialPosition = resolveCodeLocation initialPosition
        let initialVertexInInnerGraph = codeLocationToVertex.[resolvedInitialPosition]
        let resolvedFinalPosition = resolveCodeLocation stateWithNewPosition.CodeLocation
        let finalVertexInnerGraph = codeLocationToVertex.[resolvedFinalPosition]
        let transitedToAnotherBlock = initialVertexInInnerGraph <> finalVertexInnerGraph
        if transitedToAnotherBlock
        then
            let startVertex, _ = addStartVertex stateWithNewPosition
            let previousStartVertex = stateToStartVertex.[stateWithNewPosition]
            stateToStartVertex.[stateWithNewPosition] <- startVertex
            let removed = startVertexToStates.[previousStartVertex].Remove stateWithNewPosition
            assert removed
            queryEngine.AddStartVertex startVertex
            if startVertexToStates.[previousStartVertex].Count = 0
            then queryEngine.RemoveStartVertex previousStartVertex
        let forkedStartVerticesAndResolvedLocations = forks |> Seq.map addStartVertex |> Seq.cache
        let forkedStartVertices = forkedStartVerticesAndResolvedLocations |> Seq.map fst |> Array.ofSeq
        queryEngine.AddStartVertices forkedStartVertices
        if transitedToAnotherBlock || not <| Array.isEmpty forkedStartVertices then
            visualizer.VisualizeStep resolvedInitialPosition resolvedFinalPosition (forkedStartVerticesAndResolvedLocations |> Seq.map snd)

    let addStates (states:array<IGraphTrackableState>) =
        let startVertices = states |> Array.map (fun state ->
            let startVertex, resolvedLocation = addStartVertex state
            visualizer.AddMarker resolvedLocation
            startVertex)
        queryEngine.AddStartVertices startVertices
        visualizer.VisualizeGraph()

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
                    | AddGoals positions ->
                        positions
                        |> Array.map getVertexByCodeLocation 
                        |> queryEngine.AddFinalVertices 
                    | RemoveGoal pos ->
                        getVertexByCodeLocation pos
                        |> queryEngine.RemoveFinalVertex
                    | AddStates states -> Array.ofSeq states |> addStates 
                    | MoveState(_from, _to, _forks) ->
                        tryGetCfgInfo _to.CodeLocation.method |> ignore                            
                        moveState _from _to _forks |> ignore
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
    (*
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
*)
    do
        messagesProcessor.Error.Add(fun e ->
            Logger.error $"Something wrong in application graph messages processor: \n %A{e} \n %s{e.Message} \n %s{e.StackTrace}"
            raise e
            )

    member this.GetCfg (methodBase: MethodBase) =        
         messagesProcessor.PostAndReply (fun ch -> AddCFG (Some ch, methodBase))
        //tryGetCfgInfo methodBase
            
    member this.RegisterMethod (methodBase: MethodBase) =            
        messagesProcessor.Post (AddCFG (None, methodBase))        
        //tryGetCfgInfo methodBase |> ignore           
    
    member this.AddCallEdge (sourceLocation : codeLocation) (targetLocation : codeLocation) =        
        messagesProcessor.Post <| AddCallEdge (sourceLocation, targetLocation)
        //tryGetCfgInfo sourceLocation.method |> ignore
        //tryGetCfgInfo targetLocation.method |> ignore                       
        //addCallEdge sourceLocation targetLocation
        //toDot "cfg_prof.dot"

    member this.AddState (state:IGraphTrackableState) =            
        messagesProcessor.Post <| AddStates [|state|]
        //[|state|] |> addStates
        
    member this.AddStates (states:seq<IGraphTrackableState>) =            
        messagesProcessor.Post <| AddStates states
        //Array.ofSeq states |> addStates
        
    member this.MoveState (fromLocation : codeLocation) (toLocation : IGraphTrackableState) (forks : seq<IGraphTrackableState>) =
        messagesProcessor.Post <| MoveState (fromLocation, toLocation, forks)
        //tryGetCfgInfo toLocation.CodeLocation.method |> ignore                            
        //moveState fromLocation toLocation

    member x.AddGoal (location:codeLocation) =
        messagesProcessor.Post <| AddGoals [|location|]
        //[|location|]
        //|> Array.map getVertexByCodeLocation 
        //|> queryEngine.AddFinalVertices
    
    member x.AddGoals (locations:array<codeLocation>) =
        messagesProcessor.Post <| AddGoals locations
        //locations
        //|> Array.map getVertexByCodeLocation 
        //|> queryEngine.AddFinalVertices
    
    member x.RemoveGoal (location:codeLocation) =
        messagesProcessor.Post <| RemoveGoal location
        //getVertexByCodeLocation location
        //|> queryEngine.RemoveFinalVertex
    
    member this.GetShortestDistancesToAllGoalsFromStates (states: array<codeLocation>) =
        messagesProcessor.PostAndReply (fun ch -> GetShortestDistancesToGoals(ch, states))
        //ResizeArray<_>()
        
    member this.GetDistanceToNearestGoal (states: seq<IGraphTrackableState>) =
        messagesProcessor.PostAndReply (fun ch -> GetDistanceToNearestGoal(ch, states))
        //let result =
        //    states
        //    |> Seq.choose (fun state ->
        //        match queryEngine.GetDistanceToNearestGoal stateToStartVertex.[state] with
        //        | Some (_,distance) -> Some (state, int distance)
        //        | None -> None)
        //result
            
    member this.GetGoalsReachableFromStates (states: array<codeLocation>) =            
        messagesProcessor.PostAndReply (fun ch -> GetReachableGoals(ch, states))
        //Dictionary<_,_>()

    member this.CFGs with get() = cfgs.Values :> seq<CfgInfo>

    member this.SetVisualizer (v : IVisualizer) =
        visualizer <- v

module CFG =
    let applicationGraph = ApplicationGraph()
