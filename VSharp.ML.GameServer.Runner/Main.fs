open System.IO
open System.Reflection
open Argu
open Microsoft.FSharp.Core
open Suave
open Suave.Operators
open Suave.Filters
open Suave.Logging
open Suave.Sockets
open Suave.Sockets.Control
open Suave.WebSocket
open VSharp
open VSharp.Core
open VSharp.Interpreter.IL
open VSharp.ML.GameServer.Messages
open VSharp.ML.GameServer.Maps
open VSharp.Runner
   
type CliArguments =
    | [<Unique>] Port of int
    | [<Unique>] CheckActualCoverage
    interface IArgParserTemplate with
        member s.Usage =
            match s with
            | Port _ -> "Port to communicate with game client."
            | CheckActualCoverage -> "Check actual coverage using external coverage tool."
            
let ws checkActualCoverage (webSocket : WebSocket) (context: HttpContext)  =
  
  socket {
    let mutable loop = true
    
    let sendResponse (message:OutgoingMessage) =
        let byteResponse =
            serializeOutgoingMessage message
            |> System.Text.Encoding.UTF8.GetBytes
            |> ByteSegment
        webSocket.send Text byteResponse true
        
    let oracle =
        let feedback =
            fun (feedback: Feedback) ->
                let res =
                    socket {
                        let message =
                            match feedback with
                            | Feedback.ServerError s -> OutgoingMessage.ServerError s
                            | Feedback.MoveReward reward -> OutgoingMessage.MoveReward reward
                            | Feedback.IncorrectPredictedStateId i -> OutgoingMessage.IncorrectPredictedStateId i
                        do! sendResponse message
                    }
                match Async.RunSynchronously res with
                | Choice1Of2 () -> ()
                | Choice2Of2 error -> failwithf $"Error: %A{error}"
                
        let predict =
            fun (gameState:GameState) ->
                let res = 
                    socket {
                        do! sendResponse (ReadyForNextStep gameState)
                        let! msg = webSocket.read()
                        let res = 
                            match msg with
                            | (Text, data, true) ->
                                let msg = deserializeInputMessage data
                                match msg with
                                | Step stepParams -> (stepParams.StateId, stepParams.PredictedStateUsefulness)
                                | _ -> failwithf $"Unexpected message: %A{msg}"
                            | _ -> failwithf $"Unexpected message: %A{msg}"
                        return res
                    }
                match Async.RunSynchronously res with
                | Choice1Of2 (i, f) -> (i, f)
                | Choice2Of2 error -> failwithf $"Error: %A{error}"
        
        Oracle(predict,feedback)
        
    let mutable inTrainMode = true
    let runnerDir = DirectoryInfo(Directory.GetCurrentDirectory())
                    
    
    while loop do
        let! msg = webSocket.read()
        match msg with
        | (Text, data, true) ->
                let message = deserializeInputMessage data
                match message with
                | GetTrainMaps ->
                    inTrainMode <- true
                    do! sendResponse (Maps trainMaps.Values)
                | GetValidationMaps ->
                    inTrainMode <- false
                    do! sendResponse (Maps validationMaps.Values)
                | Start gameStartParams ->
                    let settings =
                        if inTrainMode
                        then trainMaps.[gameStartParams.MapId]
                        else validationMaps.[gameStartParams.MapId]
                    let assembly = RunnerProgram.ResolveAssembly <| FileInfo settings.AssemblyFullName
                    let actualCoverage = 
                        match settings.CoverageZone with
                        | CoverageZone.Method ->
                            let method = RunnerProgram.ResolveMethod(assembly, settings.NameOfObjectToCover)
                            let statistics = TestGenerator.Cover(method, oracle = oracle, searchStrategy = SearchStrategy.AI, coverageToSwitchToAI = uint settings.CoverageToStart, stepsToPlay = gameStartParams.StepsToPlay, solverTimeout=2)

                            if checkActualCoverage
                            then 
                                let testsDir = statistics.OutputDir 
                                let _expectedCoverage = 100
                                let testChecker = TestResultsChecker(testsDir, runnerDir, _expectedCoverage)
                                let exploredMethodInfo = AssemblyManager.NormalizeMethod method
                                let status,actualCoverage = testChecker.Check(exploredMethodInfo :?> MethodInfo)
                                printfn $"Actual coverage: {actualCoverage}"
                                actualCoverage
                            else System.Nullable()
                            
                        | CoverageZone.Class ->
                            let _type = RunnerProgram.ResolveType(assembly, settings.NameOfObjectToCover)
                            TestGenerator.Cover(_type, oracle = oracle, searchStrategy = SearchStrategy.AI, coverageToSwitchToAI = uint settings.CoverageToStart, stepsToPlay = gameStartParams.StepsToPlay, solverTimeout=2) |> ignore
                            System.Nullable()
                        | x -> failwithf $"Unexpected coverage zone: %A{x}"
                    
                    Application.reset()
                    API.Reset()
                    do! sendResponse (GameOver actualCoverage)
                | x -> failwithf $"Unexpected message: %A{x}"
                
        | (Close, _, _) ->
                let emptyResponse = [||] |> ByteSegment
                do! webSocket.send Close emptyResponse true
                loop <- false
        | _ -> ()
    }
  
let app checkActualCoverage : WebPart =
    choose [
        path "/gameServer" >=> handShake (ws checkActualCoverage)
    ]
    
[<EntryPoint>]
let main args =
    let parser = ArgumentParser.Create<CliArguments>(programName = "VSharp.ML.GameServer.Runner.exe")
    let args = parser.Parse args
    let checkActualCoverage =
        match args.TryGetResult <@CheckActualCoverage@> with
        | Some _ -> true
        | None -> false
    let port =
        match args.TryGetResult <@Port@> with
        | Some port -> port
        | None -> 8080
    
    startWebServer {defaultConfig with
                        logger = Targets.create Verbose [||]
                        bindings = [HttpBinding.createSimple HTTP "127.0.0.1" port]} (app checkActualCoverage)
    0