module Bench where

import Control.Exception (SomeException, evaluate, try)
import Data.Array
import Data.List (foldl', intercalate)
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as M
import Data.Ratio
import System.CPUTime (getCPUTime)
import System.Exit (die)
import Text.Read (readMaybe)

import Compiled
import Demo (hamming, mult, paper, primegame)
import Fractran
import Others (naive', regBased)

data Config = Config
  { cfgScenario :: Maybe String
  , cfgProgram :: String
  , cfgEngine :: String
  , cfgInit :: Integer
  , cfgTake :: Int
  , cfgCycleLen :: Int
  , cfgMode :: String
  , cfgCheckpointPolicy :: String
  , cfgRepeats :: Int
  , cfgOutput :: Maybe FilePath
  }

data Scenario = Scenario
  { scName :: String
  , scProgram :: String
  , scInit :: Integer
  , scTake :: Int
  , scCycleLen :: Int
  }

data RunRecord = RunRecord
  { rrScenario :: String
  , rrProgram :: String
  , rrEngine :: String
  , rrMode :: String
  , rrCheckpointPolicy :: String
  , rrInit :: Integer
  , rrLogicalStepsTarget :: Maybe Integer
  , rrLogicalStepsReached :: Integer
  , rrLogicalStepsOvershoot :: Maybe Integer
  , rrEmittedStates :: Int
  , rrChecksum :: Maybe Integer
  , rrFinalStateHash :: Maybe String
  , rrCpuSeconds :: Maybe Double
  , rrOk :: Bool
  , rrError :: Maybe String
  , rrRepeat :: Int
  }

defaultConfig :: Config
defaultConfig =
  Config
    { cfgScenario = Nothing
    , cfgProgram = "primegame"
    , cfgEngine = "cycle"
    , cfgInit = 2
    , cfgTake = 100
    , cfgCycleLen = 2
    , cfgMode = "logical-steps"
    , cfgCheckpointPolicy = "at-least"
    , cfgRepeats = 1
    , cfgOutput = Nothing
    }

usage :: String
usage =
  unlines
    [ "Usage: fractran-bench [--scenario NAME] [--program NAME] [--engine NAME] [--init N] [--take N] [--cycle-len N] [--mode logical-steps|emitted-states] [--checkpoint-policy exact|at-least] [--repeats N] [--output PATH]"
    , ""
    , "Programs: primegame, paper, hamming, mult"
    , "Engines: naive-fast, reg, frac-opt, cycle, compiled, lut"
    , "Scenarios: mult_smoke, primegame_small, primegame_medium, primegame_large"
    ]

defaultScenarioName :: Config -> String
defaultScenarioName cfg =
  fromMaybe
    (cfgProgram cfg ++ "_" ++ cfgMode cfg ++ "_" ++ show (cfgTake cfg))
    (cfgScenario cfg)

scenarios :: [Scenario]
scenarios =
  [ Scenario "mult_smoke" "mult" 2 2 2
  , Scenario "primegame_small" "primegame" 2 1000 2
  , Scenario "primegame_medium" "primegame" 2 10000 2
  , Scenario "primegame_large" "primegame" 2 100000 2
  ]

lookupScenario :: String -> Either String Scenario
lookupScenario name =
  case filter ((== name) . scName) scenarios of
    [scenario] -> Right scenario
    _ -> Left ("Unknown scenario: " ++ name)

applyScenario :: Config -> Scenario -> Config
applyScenario cfg scenario =
  cfg
    { cfgScenario = Just (scName scenario)
    , cfgProgram = scProgram scenario
    , cfgInit = scInit scenario
    , cfgTake = scTake scenario
    , cfgCycleLen = scCycleLen scenario
    }

parseArgs :: [String] -> Either String Config
parseArgs = go defaultConfig
  where
    go cfg [] = Right cfg
    go cfg ("--scenario" : value : rest) =
      case lookupScenario value of
        Right scenario -> go (applyScenario cfg scenario) rest
        Left err -> Left err
    go cfg ("--program" : value : rest) = go cfg {cfgProgram = value} rest
    go cfg ("--engine" : value : rest) = go cfg {cfgEngine = value} rest
    go cfg ("--init" : value : rest) =
      case readMaybe value of
        Just n -> go cfg {cfgInit = n} rest
        Nothing -> Left ("Invalid integer for --init: " ++ value)
    go cfg ("--take" : value : rest) =
      case readMaybe value of
        Just n -> go cfg {cfgTake = n} rest
        Nothing -> Left ("Invalid integer for --take: " ++ value)
    go cfg ("--cycle-len" : value : rest) =
      case readMaybe value of
        Just n -> go cfg {cfgCycleLen = n} rest
        Nothing -> Left ("Invalid integer for --cycle-len: " ++ value)
    go cfg ("--mode" : value : rest) = go cfg {cfgMode = value} rest
    go cfg ("--checkpoint-policy" : value : rest) = go cfg {cfgCheckpointPolicy = value} rest
    go cfg ("--repeats" : value : rest) =
      case readMaybe value of
        Just n -> go cfg {cfgRepeats = n} rest
        Nothing -> Left ("Invalid integer for --repeats: " ++ value)
    go cfg ("--output" : value : rest) = go cfg {cfgOutput = Just value} rest
    go _ ("--help" : _) = Left usage
    go _ ("-h" : _) = Left usage
    go _ (flag : _) = Left ("Unknown argument: " ++ flag ++ "\n\n" ++ usage)

lookupProgram :: String -> Either String [Rational]
lookupProgram name =
  case name of
    "primegame" -> Right primegame
    "paper" -> Right paper
    "hamming" -> Right hamming
    "mult" -> Right mult
    _ -> Left ("Unknown program: " ++ name)

enginePoints :: Config -> [Rational] -> Either String [(Integer, IntMap)]
enginePoints cfg program =
  case cfgEngine cfg of
    "naive-fast" -> Right $ zip [1 ..] $ map facmap $ naive' program (cfgInit cfg)
    "reg" -> Right $ zip [1 ..] $ regBased program (cfgInit cfg)
    "frac-opt" -> Right $ zip [1 ..] $ fracOpt program (cfgInit cfg)
    "cycle" -> Right $ stepCount $ cycles (cfgCycleLen cfg) program (cfgInit cfg)
    "compiled" -> Right $ zip [1 ..] $ runCompiled compiled (cfgInit cfg)
    "lut" ->
      case runLut compiled (cfgInit cfg) of
        Right states -> Right $ zip [1 ..] states
        Left err -> Left err
    _ -> Left ("Unknown engine: " ++ cfgEngine cfg)
  where
    compiled = compileProgram program

validateConfig :: Config -> Either String ()
validateConfig cfg
  | cfgTake cfg <= 0 = Left "--take must be positive"
  | cfgCycleLen cfg <= 0 = Left "--cycle-len must be positive"
  | cfgInit cfg <= 0 = Left "--init must be positive"
  | cfgRepeats cfg <= 0 = Left "--repeats must be positive"
  | cfgEngine cfg `elem` ["naive-fast", "reg", "frac-opt", "cycle", "compiled", "lut"] =
      Right ()
  | cfgMode cfg `notElem` ["logical-steps", "emitted-states"] =
      Left ("Unknown mode: " ++ cfgMode cfg)
  | cfgCheckpointPolicy cfg `notElem` ["exact", "at-least"] =
      Left ("Unknown checkpoint policy: " ++ cfgCheckpointPolicy cfg)
  | otherwise = Left ("Unknown engine: " ++ cfgEngine cfg)

trimPoints :: Config -> [(Integer, IntMap)] -> [(Integer, IntMap)]
trimPoints cfg =
  case cfgMode cfg of
    "logical-steps" -> takeUntilLogical (toInteger $ cfgTake cfg)
    "emitted-states" -> take (cfgTake cfg)
    _ -> take (cfgTake cfg)

takeUntilLogical :: Integer -> [(Integer, IntMap)] -> [(Integer, IntMap)]
takeUntilLogical _ [] = []
takeUntilLogical target (point@(logicalSteps, _) : rest)
  | logicalSteps >= target = [point]
  | otherwise = point : takeUntilLogical target rest

summarize :: [(Integer, IntMap)] -> (Integer, Int, Maybe Integer, Maybe String)
summarize states = (logicalStepsReached, emittedStates, checksum, finalHash)
  where
    emittedStates = length states
    logicalStepsReached =
      if null states
        then 0
        else fst (last states)
    checksum =
      if null states
        then Nothing
        else Just $ foldl' (\acc (_, im) -> acc + unfmap im) 0 states
    finalHash =
      if null states
        then Nothing
        else Just $ show $ stateHash $ snd (last states)

summarizeCompiledTrace :: CompiledProgram -> [(ExpVec, Integer)] -> (Integer, Int, Maybe Integer, Maybe String)
summarizeCompiledTrace program states = (logicalStepsReached, emittedStates, checksum, finalHash)
  where
    emittedStates = length states
    logicalStepsReached = toInteger emittedStates
    checksum =
      if null states
        then Nothing
        else Just $ foldl' (\acc (_, value) -> acc + value) 0 states
    finalHash =
      if null states
        then Nothing
        else Just $ show $ expVecStateHash program (fst (last states))

stateHash :: IntMap -> Integer
stateHash = foldl' step 1469598103934665603 . M.toAscList
  where
    step acc (prime, exponent) =
      ((acc * 1099511628211) + fromIntegral prime * 1000003 + exponent)

runOnce :: Config -> Int -> IO RunRecord
runOnce cfg repeatIx = do
  case validateConfig cfg of
    Left err -> die err
    Right () -> pure ()
  program <-
    case lookupProgram (cfgProgram cfg) of
      Right p -> pure p
      Left err -> die err
  let scenarioName = defaultScenarioName cfg
      logicalTarget =
        case cfgMode cfg of
          "logical-steps" -> Just (toInteger $ cfgTake cfg)
          _ -> Nothing
      compiled = compileProgram program
  if cfgEngine cfg == "compiled"
    then runCompiledOnce cfg compiled scenarioName logicalTarget repeatIx
    else case enginePoints cfg program of
    Left err ->
      pure $
        RunRecord
          { rrScenario = scenarioName
          , rrProgram = cfgProgram cfg
          , rrEngine = cfgEngine cfg
          , rrMode = cfgMode cfg
          , rrCheckpointPolicy = cfgCheckpointPolicy cfg
          , rrInit = cfgInit cfg
          , rrLogicalStepsTarget = logicalTarget
          , rrLogicalStepsReached = 0
          , rrLogicalStepsOvershoot = Nothing
          , rrEmittedStates = 0
          , rrChecksum = Nothing
          , rrFinalStateHash = Nothing
          , rrCpuSeconds = Nothing
          , rrOk = False
          , rrError = Just err
          , rrRepeat = repeatIx
          }
    Right basePoints -> do
      let trimmed = trimPoints cfg basePoints
      start <- getCPUTime
      result <- try (evaluateSummary trimmed) :: IO (Either SomeException (Integer, Int, Maybe Integer, Maybe String))
      end <- getCPUTime
      pure $
        case result of
          Right (logicalReached, emittedStates, checksum, finalHash) ->
            RunRecord
              { rrScenario = scenarioName
              , rrProgram = cfgProgram cfg
              , rrEngine = cfgEngine cfg
              , rrMode = cfgMode cfg
              , rrCheckpointPolicy = cfgCheckpointPolicy cfg
              , rrInit = cfgInit cfg
              , rrLogicalStepsTarget = logicalTarget
              , rrLogicalStepsReached = logicalReached
              , rrLogicalStepsOvershoot = calcOvershoot logicalTarget logicalReached
              , rrEmittedStates = emittedStates
              , rrChecksum = checksum
              , rrFinalStateHash = finalHash
              , rrCpuSeconds = Just (fromIntegral (end - start) / 1.0e12)
              , rrOk = checkpointSatisfied (cfgCheckpointPolicy cfg) logicalTarget logicalReached
              , rrError = Nothing
              , rrRepeat = repeatIx
              }
          Left err ->
            RunRecord
              { rrScenario = scenarioName
              , rrProgram = cfgProgram cfg
              , rrEngine = cfgEngine cfg
              , rrMode = cfgMode cfg
              , rrCheckpointPolicy = cfgCheckpointPolicy cfg
              , rrInit = cfgInit cfg
              , rrLogicalStepsTarget = logicalTarget
              , rrLogicalStepsReached = 0
              , rrLogicalStepsOvershoot = Nothing
              , rrEmittedStates = 0
              , rrChecksum = Nothing
              , rrFinalStateHash = Nothing
              , rrCpuSeconds = Just (fromIntegral (end - start) / 1.0e12)
              , rrOk = False
              , rrError = Just (show err)
              , rrRepeat = repeatIx
              }

runCompiledOnce :: Config -> CompiledProgram -> String -> Maybe Integer -> Int -> IO RunRecord
runCompiledOnce cfg compiled scenarioName logicalTarget repeatIx = do
  let states = trimCompiledTrace cfg (runCompiledTrace compiled (cfgInit cfg))
  start <- getCPUTime
  result <- try (evaluateCompiledSummary compiled states) :: IO (Either SomeException (Integer, Int, Maybe Integer, Maybe String))
  end <- getCPUTime
  pure $
    case result of
      Right (logicalReached, emittedStates, checksum, finalHash) ->
        RunRecord
          { rrScenario = scenarioName
          , rrProgram = cfgProgram cfg
          , rrEngine = cfgEngine cfg
          , rrMode = cfgMode cfg
          , rrCheckpointPolicy = cfgCheckpointPolicy cfg
          , rrInit = cfgInit cfg
          , rrLogicalStepsTarget = logicalTarget
          , rrLogicalStepsReached = logicalReached
          , rrLogicalStepsOvershoot = calcOvershoot logicalTarget logicalReached
          , rrEmittedStates = emittedStates
          , rrChecksum = checksum
          , rrFinalStateHash = finalHash
          , rrCpuSeconds = Just (fromIntegral (end - start) / 1.0e12)
          , rrOk = checkpointSatisfied (cfgCheckpointPolicy cfg) logicalTarget logicalReached
          , rrError = Nothing
          , rrRepeat = repeatIx
          }
      Left err ->
        RunRecord
          { rrScenario = scenarioName
          , rrProgram = cfgProgram cfg
          , rrEngine = cfgEngine cfg
          , rrMode = cfgMode cfg
          , rrCheckpointPolicy = cfgCheckpointPolicy cfg
          , rrInit = cfgInit cfg
          , rrLogicalStepsTarget = logicalTarget
          , rrLogicalStepsReached = 0
          , rrLogicalStepsOvershoot = Nothing
          , rrEmittedStates = 0
          , rrChecksum = Nothing
          , rrFinalStateHash = Nothing
          , rrCpuSeconds = Just (fromIntegral (end - start) / 1.0e12)
          , rrOk = False
          , rrError = Just (show err)
          , rrRepeat = repeatIx
          }

runBench :: Config -> IO ()
runBench cfg = do
  records <- mapM (runOnce cfg) [1 .. cfgRepeats cfg]
  mapM_ emitRecord records
  case cfgOutput cfg of
    Just path -> appendFile path (unlines $ map toJsonLine records)
    Nothing -> pure ()

emitRecord :: RunRecord -> IO ()
emitRecord record = do
  putStrLn ("scenario=" ++ rrScenario record)
  putStrLn ("program=" ++ rrProgram record)
  putStrLn ("engine=" ++ rrEngine record)
  putStrLn ("mode=" ++ rrMode record)
  putStrLn ("checkpoint_policy=" ++ rrCheckpointPolicy record)
  putStrLn ("init=" ++ show (rrInit record))
  putStrLn ("logical_steps_target=" ++ maybe "null" show (rrLogicalStepsTarget record))
  putStrLn ("logical_steps_reached=" ++ show (rrLogicalStepsReached record))
  putStrLn ("logical_steps_overshoot=" ++ maybe "null" show (rrLogicalStepsOvershoot record))
  putStrLn ("emitted_states=" ++ show (rrEmittedStates record))
  putStrLn ("checksum=" ++ maybe "null" show (rrChecksum record))
  putStrLn ("final_state_hash=" ++ maybe "null" id (rrFinalStateHash record))
  putStrLn ("cpu_seconds=" ++ maybe "null" show (rrCpuSeconds record))
  putStrLn ("ok=" ++ show (rrOk record))
  putStrLn ("error=" ++ maybe "null" id (rrError record))
  putStrLn ("repeat=" ++ show (rrRepeat record))

evaluateSummary :: [(Integer, IntMap)] -> IO (Integer, Int, Maybe Integer, Maybe String)
evaluateSummary states = evaluate forced
  where
    forced =
      let summary@(logicalReached, emittedStates, checksum, finalHash) = summarize states
       in logicalReached `seq` emittedStates `seq` checksum `seq` finalHash `seq` summary

evaluateCompiledSummary :: CompiledProgram -> [(ExpVec, Integer)] -> IO (Integer, Int, Maybe Integer, Maybe String)
evaluateCompiledSummary program states = evaluate forced
  where
    forced =
      let summary@(logicalReached, emittedStates, checksum, finalHash) = summarizeCompiledTrace program states
       in logicalReached `seq` emittedStates `seq` checksum `seq` finalHash `seq` summary

trimCompiledTrace :: Config -> [(ExpVec, Integer)] -> [(ExpVec, Integer)]
trimCompiledTrace cfg =
  case cfgMode cfg of
    "logical-steps" -> take (cfgTake cfg)
    "emitted-states" -> take (cfgTake cfg)
    _ -> take (cfgTake cfg)

toJsonLine :: RunRecord -> String
toJsonLine record =
  "{" ++ intercalate "," fields ++ "}"
  where
    fields =
      [ jsonField "scenario" (jsonString $ rrScenario record)
      , jsonField "program" (jsonString $ rrProgram record)
      , jsonField "engine" (jsonString $ rrEngine record)
      , jsonField "mode" (jsonString $ rrMode record)
      , jsonField "checkpoint_policy" (jsonString $ rrCheckpointPolicy record)
      , jsonField "init" (show $ rrInit record)
      , jsonField "logical_steps_target" (maybe "null" show $ rrLogicalStepsTarget record)
      , jsonField "logical_steps_reached" (show $ rrLogicalStepsReached record)
      , jsonField "logical_steps_overshoot" (maybe "null" show $ rrLogicalStepsOvershoot record)
      , jsonField "emitted_states" (show $ rrEmittedStates record)
      , jsonField "checksum" (maybe "null" show $ rrChecksum record)
      , jsonField "final_state_hash" (maybe "null" jsonString $ rrFinalStateHash record)
      , jsonField "cpu_seconds" (maybe "null" show $ rrCpuSeconds record)
      , jsonField "ok" (if rrOk record then "true" else "false")
      , jsonField "error" (maybe "null" jsonString $ rrError record)
      , jsonField "repeat" (show $ rrRepeat record)
      ]

jsonField :: String -> String -> String
jsonField key value = jsonString key ++ ":" ++ value

jsonString :: String -> String
jsonString value = "\"" ++ concatMap escapeChar value ++ "\""

escapeChar :: Char -> String
escapeChar '"' = "\\\""
escapeChar '\\' = "\\\\"
escapeChar '\n' = "\\n"
escapeChar '\r' = "\\r"
escapeChar '\t' = "\\t"
escapeChar c = [c]

checkpointSatisfied :: String -> Maybe Integer -> Integer -> Bool
checkpointSatisfied _ Nothing _ = True
checkpointSatisfied "exact" (Just target) reached = reached == target
checkpointSatisfied "at-least" (Just target) reached = reached >= target
checkpointSatisfied _ _ _ = False

calcOvershoot :: Maybe Integer -> Integer -> Maybe Integer
calcOvershoot Nothing _ = Nothing
calcOvershoot (Just target) reached = Just (max 0 (reached - target))
