{-# LANGUAGE OverloadedStrings #-}
{- compile:
hastec --onexec -O2 --opt-all  Browser.hs -o web/fractran.js
java -jar compiler.jar --compilation_level ADVANCED_OPTIMIZATIONS --jscomp_off globalThis fractran.js --js_output_file web/fractran.min.js
-}
import qualified Data.Map.Strict as M

import Haste.Foreign
import Haste.Prim (toJSStr)

import Fractran


run :: ([Rational] -> IntMap -> [(Integer, IntMap)]) -> String -> String -> String
run fn fstr input = show $ last $ fn fracs imap where
  fracs = read fstr
  imap = M.fromList $ read input
runF :: ([Rational] -> Integer -> [(Integer, IntMap)]) -> String -> String -> String
runF fn fstr input = show $ last $ fn fracs i where
  fracs = read fstr
  i =  read input

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

main = do
  export "runReg" runReg
  export "runRegF" runRegF
  export "runCyc" runCyc
  export "runCycF" runCycF

{-
Haste.runReg('[1%2]', '[(2,100)]');
Haste.runRegF('[1%2]', '1024');
Haste.runCyc(2, '[1%2]', '[(2,100)]');
Haste.runCycF('[1%2]', '1024');
-}