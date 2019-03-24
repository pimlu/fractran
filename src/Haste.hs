{-# LANGUAGE OverloadedStrings #-}
{- compile:
hastec --onexec -O2 --opt-all  Browser.hs -o web/fractran.js
java -jar compiler.jar --compilation_level ADVANCED_OPTIMIZATIONS --jscomp_off globalThis fractran.js --js_output_file web/fractran.min.js
-}

import Haste.Foreign
import Haste.Prim (toJSStr)

import Browser

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
