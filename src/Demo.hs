{-# LANGUAGE MagicHash #-}
module Demo where

import Data.Ratio
import GHC.Exts
import GHC.Integer.Logarithms
import qualified Data.Map.Strict as M
import System.IO
import Data.Char
import Data.Maybe

import Fractran
import Others

cyclesIM :: Int -> [Rational] -> Integer -> [IntMap]
cyclesIM cl f i = [im | Step im <- cs]
    where cs = cycles cl f i
cyclesIM' :: Int -> [Rational] -> IntMap -> [IntMap]
cyclesIM' cl f i = [im | Step im <- cs]
    where cs = cycles' cl f i

primegame = [17%91, 78%85, 19%51, 23%38, 29%33, 77%29, 95%23, 77%19, 1%17, 11%13, 13%11, 15%2, 1%7, 55]
paper=[7%11,(5*13*11)%(2*7),(5*17*11)%(3*7),1%7,2%13,3%17]
hamming = [3*11%(2^2*5), 5%11, 13%(2*5), 1%5, 2%3, 2*5%7, 7%2]
fteval = [197*103%(2^11*101), 101%103, 103*127%(2*101), 101%103, 109%101,
  2*23%(197*109), 109%23, 29%109,197*41*47%(31*59), 11^10*53%(127*197), 197%53,
  37%197, 7^10*43%(11^10*37), 37%43, 59%(37*47), 59%47, 41*61%59, 31*67%(41*61),
  61%67, 7*67%(127*61), 61%67,101%71, 73%(127^9*29), 79%(127^2*73),
  83%(127*73), 89%(2*29), 163%29, 127^11*89%79, 337%83, 2*59%89, 71%61,
  7*173%(127*163), 163%173, 337*167%163, 347%(31*337), 337%347, 151%337,
  1%71,19*179%(3*7*193), 193%179, 157%(7*193), 17*181%193, 7*211%(19*181),
  181%211, 193%181, 157%193, 223%(7*157), 157%223, 281*283%239,
  3*257*269%(7*241), 241%269, 263%241, 7*271%(257*263), 263%271, 281%263,
  241%(17*281), 1%281, 307%(7*283), 283%307, 293%283, 71*131%107, 193%(131*151),
  227%(19*157), 71*311%227, 233%(151*167*311), 151*311%229, 7*317%(19*229),
  229%317, 239*331%217, 71*313%157, 239*251%(151*167*313), 239*251%(151*313),
  149%(251*293), 107%(293*331), 137%199, 2^100*13^100*353%(5^100*137),
  2*13*353%(5*137), 137%353, 349%137, 107%349, 5^100*359%(13^100*149),
  5*359%(13*149), 149%359, 199%149]
nonterm = [(2*3)%5, (5*3)%2, 1%3]
mult = map (uncurry (%)) [(455, 33), (11, 13), (1, 11), (3, 7), (11, 2), (1, 3)]

powers :: Integer -> [Integer] -> [Integer]
powers k vs = [ilog k v | v<-vs, k^ilog k v == v]

ilog k v = fromIntegral $ I# (integerLogBase# k v)

liveout str = do
  hFlush stdout
  mapM (\c -> putStr [c] >> hFlush stdout) $ show str ++ "\n"

dopg view interp k = liveout $ take k $ view 2 $ interp primegame 2


hammingMain k = do
  let ham = naive hamming $ 2^(2^k-1)
  putStrLn $ (show $ length ham) ++ " iterations"
  liveout $ powers 13 $ (:[]) . last $ ham
hammingMainFO k = do
  let ham = zip [1..] $ regBased' hamming $ M.fromList [(2, (2^k-1))]
  putStrLn $ (show $ fst $ last $ ham) ++ " iterations"
  liveout $ mapGetPow 13 $ (:[]) . snd . last $ ham
hammingMain' k = do
  let ham = stepCount $ (cycles' 2) hamming $ M.fromList [(2, (2^k-1))]
  putStrLn $ (show $ fst $ last $ ham) ++ " iterations"
  liveout $ mapGetPow 13 $ (:[]) . snd . last $ ham

ftin = M.fromList [(3,2^6*3^6), (5,475), (199,1)]
ftin' = M.fromList [(3,3^1*5^1), (5,5211222), (199,1)]
ftin'' = M.fromList [(3,2^0*3^0), (5,3079784207925154324249736405657), (199,1)]

ftMapGetPow l = [if f3>0 then Just $ facmap f3 else Nothing |
  v<-l, get0 199 v/=0, let f3 = get0 3 v]
naiveSelfInterp inp = do
  liveout . facmap $ last $ naive fteval $ unfmap inp
smartSelfInterp method inp = do
  liveout $ ftMapGetPow $ method fteval inp

demo = do
  let smartpg = dopg mapGetPow
  putStrLn "Naive with 20 primes:"
  dopg powers naive' 20
  putStrLn "Register based with 30 primes:"
  smartpg regBased 30
  putStrLn "Fraction optimized with 30 primes:"
  smartpg fracOpt 30
  putStrLn "Cycle detection with 50 primes:"
  smartpg (cyclesIM 2) 50
  putStrLn "Naive hamming 2^16-1:"
  hammingMain 16
  putStrLn "Cycle hamming 2^16-1:"
  hammingMain' 16
  putStrLn "Cycle hamming 2^1000-1:"
  hammingMain' 1000

demo2 = do
  putStrLn "Naive on 1 fraction input:"
  putStrLn "[takes too long]" -- naiveSelfInterp ftin
  putStrLn "Fraction optimized on 1 fraction input:"
  smartSelfInterp fracOpt' ftin
  putStrLn "Cycle detection on 1 fraction input:"
  smartSelfInterp (cyclesIM' 16) ftin
  putStrLn "Cycle detection on 2 fraction input:"
  smartSelfInterp (cyclesIM' 16) ftin'
