module BrowserApi where

import qualified Data.Map.Strict as M

import Fractran

type EvalFn = [Rational] -> IntMap -> [(Integer, IntMap)]
type ReturnFn = [(Integer, IntMap)] -> IO String

regSim :: EvalFn
regSim f i = zip [1..] $ fracOpt' f i

cycleFn :: Int -> EvalFn
cycleFn k prog st = stepCount $ cycles' k prog st

doRun :: EvalFn -> ReturnFn -> String -> String -> IO String
doRun evalFn returnFn fractions input = returnFn result where
  result = evalFn (read fractions) (readState input)

readState :: String -> IntMap
readState state
  | head state == '[' = M.fromList $ read state
  | otherwise = facmap $ read state

runDynamic :: Int -> String -> String -> IO String
runDynamic k = doRun evalFn returnFn where
  evalFn = if k <= 1 then regSim else cycleFn k
  returnFn = return . show . last
