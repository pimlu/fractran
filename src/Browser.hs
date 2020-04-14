import Asterius.Types

import BrowserApi

hsRunDynamic :: Int -> JSString -> JSString -> IO JSString
hsRunDynamic k fractions input = fmap toJSString res where
  res = runDynamic k (fromJSString fractions) (fromJSString input)

foreign export javascript "hsRunDynamic" hsRunDynamic :: Int -> JSString -> JSString -> IO JSString

main = return ()
