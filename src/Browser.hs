import qualified Data.Map.Strict as M

import Fractran

run :: ([Rational] -> IntMap -> [(Integer, IntMap)]) -> String -> String -> String
run fn fstr input = show $ last $ fn fracs imap where
  fracs = read fstr
  imap = M.fromList $ read input
runF :: ([Rational] -> Integer -> [(Integer, IntMap)]) -> String -> String -> String
runF fn fstr input = show $ last $ fn fracs i where
  fracs = read fstr
  i = read input

runReg :: String -> String -> String
runReg = run reg where
  reg f i = zip [1..] $ fracOpt' f i
runRegF :: String -> String -> String
runRegF = runF reg where
  reg f i = zip [1..] $ fracOpt f i

runCyc :: Int -> String -> String -> String
runCyc k = run cyc where
  cyc f i = stepCount $ cycles' k f i
runCycF :: Int -> String -> String -> String
runCycF k = runF cyc where
  cyc f i = stepCount $ cycles k f i
