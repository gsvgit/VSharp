open System.IO
open System.Net.Sockets
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
open VSharp.Explorer
open VSharp.IL
open VSharp.ML.GameServer.Messages
open VSharp.Runner

[<Struct>]
type ExplorationResult =
    val ActualCoverage: uint<percent>
    val TestsCount: uint<test>
    val ErrorsCount: uint<error>
    val StepsCount: uint<step>

    new(actualCoverage, testsCount, errorsCount, stepsCount) =
        {
            ActualCoverage = actualCoverage
            TestsCount = testsCount
            ErrorsCount = errorsCount
            StepsCount = stepsCount
        }

type Mode =
    | Server = 0
    | Generator = 1
    | SendModel = 2

let TIMEOUT_FOR_TRAINING = 15 * 60
let SOLVER_TIMEOUT_FOR_TRAINING = 2

type CliArguments =
    | [<Unique>] Port of int
    | [<Unique>] DatasetBasePath of string
    | [<Unique>] DatasetDescription of string
    | [<Unique ; Mandatory>] Mode of Mode
    | [<Unique>] OutFolder of string
    | [<Unique>] StepsToSerialize of uint
    | [<Unique>] Model of string
    | [<Unique>] StepsToPlay of uint<step>
    | [<Unique>] DefaultSearcher of string
    | [<Unique>] StepsToStart of uint<step>
    | [<Unique>] AssemblyFullName of string
    | [<Unique>] NameOfObjectToCover of string
    | [<Unique>] MapName of string
    | [<Unique>] UseGPU
    | [<Unique>] Optimize

    interface IArgParserTemplate with
        member s.Usage =
            match s with
            | Port _ -> "Port to communicate with game client."
            | DatasetBasePath _ ->
                "Full path to dataset root directory. Dll location is <DatasetBasePath>/<AssemblyFullName>"
            | DatasetDescription _ -> "Full paths to JSON-file with dataset description."
            | Mode _ ->
                "Mode to run application. Server --- to train network, Generator --- to generate data for training."
            | OutFolder _ -> "Folder to store generated data."
            | StepsToSerialize _ -> "Maximal number of steps for each method to serialize."
            | Model _ -> """Path to ONNX model (use it for training in mode "SendModel")"""
            | StepsToPlay _ -> """Steps to start"""
            | DefaultSearcher _ -> """Default searcher"""
            | StepsToStart _ -> """Steps to start"""
            | AssemblyFullName _ -> """Path to dll that contains game map"""
            | NameOfObjectToCover _ -> """Name of object to cover"""
            | MapName _ -> """Name of map"""
            | UseGPU -> "Specifies whether the ONNX execution session should use a CUDA-enabled GPU."
            | Optimize ->
                "Enabling options like parallel execution and various graph transformations to enhance performance of ONNX."

let mutable inTrainMode = true

let explore (gameMap: GameMap) options =
    let assembly =
        RunnerProgram.TryLoadAssembly <| FileInfo gameMap.AssemblyFullName

    let method =
        RunnerProgram.ResolveMethod (assembly, gameMap.NameOfObjectToCover)
    let statistics =
        TestGenerator.Cover (method, options)

    let actualCoverage =
        try
            let testsDir = statistics.OutputDir
            let _expectedCoverage = 100
            let exploredMethodInfo =
                AssemblyManager.NormalizeMethod method

            let status, actualCoverage, message =
                VSharp.Test.TestResultChecker.Check (testsDir, exploredMethodInfo :?> MethodInfo, _expectedCoverage)

            printfn $"Actual coverage for {gameMap.MapName}: {actualCoverage}"

            if actualCoverage < 0 then
                0u<percent>
            else
                uint actualCoverage * 1u<percent>
        with e ->
            printfn $"Coverage checking problem:{e.Message} \n {e.StackTrace}"
            0u<percent>

    ExplorationResult (
        actualCoverage,
        statistics.TestsCount * 1u<test>,
        statistics.ErrorsCount * 1u<error>,
        statistics.StepsCount * 1u<step>
    )

let getGameMap (gameMaps: ResizeArray<GameMap>) (mapName: string) =
    let mutable gameMapRes: Option<GameMap> =
        None

    for gameMap in gameMaps do
        if gameMap.MapName = mapName then
            gameMapRes <- Some gameMap

    match gameMapRes with
    | Some gameMap -> printfn ($"{gameMap.ToString}")
    | None -> printfn "map is not selected"

    gameMapRes

let loadGameMaps (datasetDescriptionFilePath: string) =
    let jsonString =
        File.ReadAllText datasetDescriptionFilePath
    let maps = ResizeArray<GameMap> ()

    for map in System.Text.Json.JsonSerializer.Deserialize<GameMap[]> jsonString do
        maps.Add map

    maps

let ws port outputDirectory (webSocket: WebSocket) (context: HttpContext) =
    let mutable loop = true

    socket {

        let sendResponse (message: OutgoingMessage) =
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
                let mutable cnt = 0u

                fun (gameState: GameState) ->
                    let toDot drawHistory =
                        let file = Path.Join ("dot", $"{cnt}.dot")
                        gameState.ToDot file drawHistory
                        cnt <- cnt + 1u
                    //toDot false
                    let res =
                        socket {
                            do! sendResponse (ReadyForNextStep gameState)
                            let! msg = webSocket.read ()

                            let res =
                                match msg with
                                | (Text, data, true) ->
                                    let msg = deserializeInputMessage data

                                    match msg with
                                    | Step stepParams -> (stepParams.StateId)
                                    | _ -> failwithf $"Unexpected message: %A{msg}"
                                | _ -> failwithf $"Unexpected message: %A{msg}"

                            return res
                        }

                    match Async.RunSynchronously res with
                    | Choice1Of2 i -> i
                    | Choice2Of2 error -> failwithf $"Error: %A{error}"

            Oracle (predict, feedback)

        while loop do
            let! msg = webSocket.read ()

            match msg with
            | (Text, data, true) ->
                let message = deserializeInputMessage data

                match message with
                | ServerStop -> loop <- false
                | Start gameMap ->
                    printfn $"Start map {gameMap.MapName}, port {port}"
                    let stepsToStart = gameMap.StepsToStart
                    let stepsToPlay = gameMap.StepsToPlay

                    let aiTrainingOptions =
                        {
                            aiBaseOptions =
                                {
                                    defaultSearchStrategy =
                                        match gameMap.DefaultSearcher with
                                        | searcher.BFS -> BFSMode
                                        | searcher.DFS -> DFSMode
                                        | x -> failwithf $"Unexpected searcher {x}. Use DFS or BFS for now."
                                    mapName = gameMap.MapName
                                }
                            stepsToSwitchToAI = stepsToStart
                            stepsToPlay = stepsToPlay
                            oracle = Some oracle
                        }

                    let aiOptions: AIOptions =
                        (Training (
                            SendEachStep
                                {
                                    aiAgentTrainingOptions = aiTrainingOptions
                                }
                        ))

                    let options =
                        VSharpOptions (
                            timeout = TIMEOUT_FOR_TRAINING,
                            outputDirectory = outputDirectory,
                            searchStrategy = SearchStrategy.AI,
                            aiOptions = (Some aiOptions |> Option.defaultValue Unchecked.defaultof<_>),
                            stepsLimit = uint (stepsToPlay + stepsToStart),
                            solverTimeout = SOLVER_TIMEOUT_FOR_TRAINING
                        )

                    let explorationResult =
                        explore gameMap options

                    Application.reset ()
                    API.Reset ()
                    HashMap.hashMap.Clear ()

                    do!
                        sendResponse (
                            GameOver (
                                explorationResult.ActualCoverage,
                                explorationResult.TestsCount,
                                explorationResult.ErrorsCount
                            )
                        )

                    printfn $"Finish map {gameMap.MapName}, port {port}"
                | x -> failwithf $"Unexpected message: %A{x}"

            | (Close, _, _) ->
                let emptyResponse = [||] |> ByteSegment
                do! webSocket.send Close emptyResponse true
                loop <- false
            | _ -> ()
    }

let app port outputDirectory : WebPart =
    choose
        [
            path "/gameServer" >=> handShake (ws port outputDirectory)
        ]

let serializeExplorationResult (explorationResult: ExplorationResult) =
    $"{explorationResult.ActualCoverage} {explorationResult.TestsCount} {explorationResult.StepsCount} {explorationResult.ErrorsCount}"

let generateDataForPretraining outputDirectory datasetBasePath (maps: ResizeArray<GameMap>) stepsToSerialize =
    for map in maps do
        if map.StepsToStart = 0u<step> then
            printfn $"Generation for {map.MapName} started."

            let map =
                GameMap (
                    map.StepsToPlay,
                    map.StepsToStart,
                    Path.Combine (datasetBasePath, map.AssemblyFullName),
                    map.DefaultSearcher,
                    map.NameOfObjectToCover,
                    map.MapName
                )

            let aiBaseOptions =
                {
                    defaultSearchStrategy = BFSMode
                    mapName = map.MapName
                }

            let options =
                VSharpOptions (
                    timeout = 5 * 60,
                    outputDirectory = outputDirectory,
                    searchStrategy = SearchStrategy.ExecutionTreeContributedCoverage,
                    stepsLimit = stepsToSerialize,
                    solverTimeout = 2,
                    aiOptions =
                        (Some (DatasetGenerator aiBaseOptions)
                         |> Option.defaultValue Unchecked.defaultof<_>)
                )

            let folderForResults =
                Serializer.getFolderToStoreSerializationResult outputDirectory map.MapName

            if Directory.Exists folderForResults then
                Directory.Delete (folderForResults, true)

            let _ =
                Directory.CreateDirectory folderForResults

            let explorationResult = explore map options

            File.WriteAllText (Path.Join (folderForResults, "result"), serializeExplorationResult explorationResult)

            printfn
                $"Generation for {map.MapName} finished with coverage {explorationResult.ActualCoverage}, tests {explorationResult.TestsCount}, steps {explorationResult.StepsCount},errors {explorationResult.ErrorsCount}."

            Application.reset ()
            API.Reset ()
            HashMap.hashMap.Clear ()

let runTrainingSendModelMode
    outputDirectory
    (gameMap: GameMap)
    (pathToModel: string)
    (useGPU: bool)
    (optimize: bool)
    (port: int)
    =
    printfn $"Run infer on {gameMap.MapName} have started."

    let aiTrainingOptions =
        {
            aiBaseOptions =
                {
                    defaultSearchStrategy =
                        match gameMap.DefaultSearcher with
                        | searcher.BFS -> BFSMode
                        | searcher.DFS -> DFSMode
                        | x -> failwithf $"Unexpected searcher {x}. Use DFS or BFS for now."

                    mapName = gameMap.MapName
                }
            stepsToSwitchToAI = gameMap.StepsToStart
            stepsToPlay = gameMap.StepsToPlay
            oracle = None
        }

    let stream =
        let host = "localhost" // TODO: working within a local network
        let client = new TcpClient ()
        client.Connect (host, port)
        client.SendBufferSize <- 2048
        Some <| client.GetStream ()

    let aiOptions: AIOptions =
        Training (
            SendModel
                {
                    aiAgentTrainingOptions = aiTrainingOptions
                    outputDirectory = outputDirectory
                    stream = stream
                }
        )

    let options =
        VSharpOptions (
            timeout = TIMEOUT_FOR_TRAINING,
            outputDirectory = outputDirectory,
            searchStrategy = SearchStrategy.AI,
            solverTimeout = SOLVER_TIMEOUT_FOR_TRAINING,
            aiOptions = (Some aiOptions |> Option.defaultValue Unchecked.defaultof<_>),
            pathToModel = pathToModel,
            useGPU = useGPU,
            optimize = optimize
        )

    let explorationResult =
        explore gameMap options

    File.WriteAllText (
        Path.Join (outputDirectory, gameMap.MapName + "result"),
        serializeExplorationResult explorationResult
    )

    printfn
        $"Running for {gameMap.MapName} finished with coverage {explorationResult.ActualCoverage}, tests {explorationResult.TestsCount}, steps {explorationResult.StepsCount},errors {explorationResult.ErrorsCount}."



[<EntryPoint>]
let main args =
    let parser =
        ArgumentParser.Create<CliArguments> (programName = "VSharp.ML.GameServer.Runner.exe")

    let args = parser.Parse args
    let mode = args.GetResult <@ Mode @>

    let port =
        match args.TryGetResult <@ Port @> with
        | Some port -> port
        | None -> 8100

    let outputDirectory =
        match args.TryGetResult <@ OutFolder @> with
        | Some path -> path
        | None -> Path.Combine (Directory.GetCurrentDirectory (), string port)

    let cleanOutputDirectory () =
        if Directory.Exists outputDirectory then
            Directory.Delete (outputDirectory, true)

        Directory.CreateDirectory outputDirectory

    printfn $"outputDir: {outputDirectory}"

    match mode with
    | Mode.Server ->
        let _ = cleanOutputDirectory ()

        try
            startWebServer
                { defaultConfig with
                    logger = Targets.create Verbose [||]
                    bindings =
                        [
                            HttpBinding.createSimple HTTP "127.0.0.1" port
                        ]
                }
                (app port outputDirectory)
        with e ->
            printfn $"Failed on port {port}"
            printfn $"{e.Message}"
    | Mode.SendModel ->
        let model =
            match args.TryGetResult <@ Model @> with
            | Some path -> path
            | None -> "models/model.onnx"

        let stepsToPlay =
            args.GetResult <@ StepsToPlay @>

        let defaultSearcher =
            let s = args.GetResult <@ DefaultSearcher @>
            let upperedS =
                String.map System.Char.ToUpper s

            match upperedS with
            | "BFS" -> searcher.BFS
            | "DFS" -> searcher.DFS
            | _ -> failwith "Use BFS or DFS as a default searcher"

        let stepsToStart =
            args.GetResult <@ StepsToStart @>
        let assemblyFullName =
            args.GetResult <@ AssemblyFullName @>
        let nameOfObjectToCover =
            args.GetResult <@ NameOfObjectToCover @>
        let mapName = args.GetResult <@ MapName @>

        let gameMap =
            GameMap (
                stepsToPlay = stepsToPlay,
                stepsToStart = stepsToStart,
                assemblyFullName = assemblyFullName,
                defaultSearcher = defaultSearcher,
                nameOfObjectToCover = nameOfObjectToCover,
                mapName = mapName
            )

        let useGPU =
            (args.TryGetResult <@ UseGPU @>).IsSome
        let optimize =
            (args.TryGetResult <@ Optimize @>).IsSome

        runTrainingSendModelMode outputDirectory gameMap model useGPU optimize port
    | Mode.Generator ->
        let datasetDescription =
            args.GetResult <@ DatasetDescription @>
        let datasetBasePath =
            args.GetResult <@ DatasetBasePath @>

        let stepsToSerialize =
            match args.TryGetResult <@ StepsToSerialize @> with
            | Some steps -> steps
            | None -> 500u

        let _ = cleanOutputDirectory ()
        let maps = loadGameMaps datasetDescription
        generateDataForPretraining outputDirectory datasetBasePath maps stepsToSerialize
    | x -> failwithf $"Unexpected mode {x}."

    0
