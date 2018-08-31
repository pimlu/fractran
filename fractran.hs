{-# LANGUAGE MagicHash #-}

import Data.Ratio
import Data.Maybe
import Data.List
import GHC.Exts
import GHC.Integer.Logarithms
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.IO
import Data.Array
import Debug.Trace
import Data.Char
import Control.Exception
import qualified Data.Sequence as Q


import qualified CBuf as B

type IntMap = M.Map Int Integer
data CycleStep = Step IntMap | Leap Integer deriving (Eq, Show)

naive :: [Rational] -> Integer -> [Integer]
naive fs n = maybe [] (next . numerator) match where
  ps = map (*fromIntegral n) fs
  match = find ((==1) . denominator) ps
  next p = p : naive fs p
naive' :: [Rational] -> Integer -> [Integer]
naive' fs n = maybe [] (next . prod) match where
  rats = [(numerator f, denominator f) | f <- fs]
  match = find (\(num, den) -> (n*num) `rem` den == 0) rats
  prod (num, den) = (n*num) `div` den
  next p = p : naive' fs p

minus :: Ord a => [a] -> [a] -> [a]
minus = minusBy compare

-- |  The 'minusBy'' function is the non-overloaded version of 'minus''.
minusBy :: (a -> b -> Ordering) -> [a] -> [b] -> [a]
minusBy cmp = loop
  where
     loop [] _ys = []
     loop xs [] = xs
     loop (x:xs) (y:ys)
       = case cmp x y of
          LT -> x : loop xs (y:ys)
          EQ ->     loop xs (y:ys)
          GT ->     loop (x:xs) ys
primes = eratos [2..] where
  eratos []     = []
  eratos (p:xs) = p : eratos (xs `minus` [p*p, p*p+p..])
factors :: Integer -> [Integer]
factors n = fac primes n where
  fac _ 1 = []
  fac (p:ps) k
    | k `rem` p == 0 = p : fac (p:ps) (k `div` p)
    | otherwise = fac ps k

times' :: IntMap -> (IntMap, IntMap) -> IntMap
times' x (num, den) = M.fromList pairs where
  keys = S.toList $ S.fromList $ M.keys x ++ M.keys num ++ M.keys den
  pairs = [(k, get0 k x + get0 k num - get0 k den) | k<-keys]

times :: IntMap -> (IntMap, IntMap) -> IntMap
{-times x (num, den) = M.foldlWithKey add subbed num where
  subbed = M.foldlWithKey sub x den
  add m k v = M.alter (Just . maybe v (+v)) k m
  sub m k v = (M.alter (nonzero . (subtract v) . fromJust) k m)
  nonzero v = whenMaybe v $ v/=0-}
times x (num, den) = fprod (fdiv x den) num
fprod x y = M.foldlWithKey add x y where
  add m k v = M.alter (Just . maybe v (+v)) k m
fdiv x y = M.foldlWithKey sub x y where
  sub m k v = (M.alter (nonzero . (subtract v) . fromJust) k m)
  nonzero v = whenMaybe v $ v/=0


get0 = M.findWithDefault 0

compat x (_, den) = all valid $ M.keys den where
  valid k = get0 k x >= get0 k den

facmap :: Integer -> IntMap
facmap n = M.fromList $ map g $ group $ factors n where
  g l = (fromIntegral $ head l, genericLength l)
unfmap :: IntMap -> Integer
unfmap m = M.foldlWithKey mul 1 m where
  mul prod prime pow = prod * toInteger prime^pow
whenMaybe _ False = Nothing
whenMaybe ma True = Just ma

regBased :: [Rational] -> Integer -> [IntMap]
regBased fracs init = regBased' fracs $ facmap init
regBased' fracs init = eval init where
  fs = [(facmap $ numerator f, facmap $ denominator f) | f<-fracs]
  match n = find (compat n) fs
  eval n = maybe [] (next . times n) $ match n
  next p = p : eval p

{-
optArr :: [(IntMap, IntMap)] -> Array Int [(Int, (IntMap, IntMap))]
optArr fs = trace msg $ listArray (0, length fs - 1) opts where
  ifs = (zip [0..] fs) :: [(Int, (IntMap, IntMap))]
  opts = [opt i f | (i,f) <- ifs] :: [[(Int, (IntMap, IntMap))]]
  opt i f = let (pre,post) = splitAt i ifs in (preOpt f pre ++ post) :: [(Int, (IntMap, IntMap))]
  preOpt (num, _) pre = (filter (couldPre num . snd . snd) pre)
  couldPre a b = not . M.null $ M.intersection a b
  msg = unlines $ [show (i, map fst o) | (i,o)<-zip [0..] opts]
-}
optArr :: [(IntMap, IntMap)] -> Array Int [(Int, (IntMap, IntMap))]
optArr fs = {-trace msg $-} listArray (0, length fs - 1) opts where
  ifs = zip [0..] fs
  opts = [opt i f | (i,f) <- ifs]
  opt i f = let (pre,post) = splitAt i ifs in (preOpt f pre ++ post)
  preOpt (num, _) pre = (filter (couldPre num . snd . snd) pre)
  couldPre a b = not . M.null $ M.intersection a b
  msg = unlines $ [show (i, map fst o) | (i,o)<-zip [0..] opts]

fracOpt :: [Rational] -> Integer -> [IntMap]
fracOpt fracs init = fracOpt' fracs $ facmap init
fracOpt' fracs init = eval ifs init  where
  fmaps = [(facmap $ numerator f, facmap $ denominator f) | f<-fracs]
  ifs = (zip [0..] fmaps) :: [(Int, (IntMap, IntMap))]
  opts = optArr fmaps
  match fs n = (find (compat n . snd) fs) :: Maybe (Int, (IntMap, IntMap))
  eval fs n = maybe [] (next . times' n) $ match fs n
  times' n (i, f) = (i, times n f)
  next (i, p) = p : (eval :: [(Int, (IntMap, IntMap))] -> IntMap -> [IntMap]) (opts ! i) p

-- -> (data, logic)
stateSplit :: IntMap -> IntMap -> (IntMap, IntMap)
stateSplit sep frac = M.partitionWithKey part frac where
  part k a = a >= M.findWithDefault 0 k sep

leap :: IntMap -> Q.Seq (IntMap, IntMap) -> (IntMap, IntMap) -> (Integer, IntMap)
leap dmaxes prev state = assert (plogic == slogic) (steps, n) where
  len = Q.length prev
  lasti = len - 1
  (pdata, plogic) = Q.index prev lasti
  (sdata, slogic) = state
  keys = M.keys $ M.union pdata sdata

  hist = toList $ Q.take lasti prev
  cs = [s | k <- keys, let s=life k, s>=0]
  diffs = fprod pdata $ M.map (0-) sdata
  life k
    | diff == 0 = -1
    | rem < 0 = 0
    | diff < 0 = -1
    | otherwise = rem `div` diff
    where
      sk = get0 k sdata
      dip = minimum $ 0:[get0 k s - sk | (s,_) <- hist]
      rem = sk + dip - (dmaxes M.! k)
      diff = get0 k diffs
  (steps, newdata) = case cs of
    [] -> error "Nonterminating cycle detected"
    _ -> let s = minimum cs in
        (fromIntegral len * s,
        fprod sdata $ M.map (* (-s)) diffs)
  n = fprod slogic newdata

cycles :: Int -> [Rational] -> Integer -> [CycleStep]
cycles cyclen fracs init = cycles' cyclen fracs $ facmap init
cycles' :: Int -> [Rational] -> IntMap -> [CycleStep]
cycles' cyclen fracs init = tail $ eval ifs obuf init where
  obuf = (B.cbuf cyclen snd []) :: B.CBuf (IntMap, IntMap) IntMap
  fmaps = [(facmap $ numerator f, facmap $ denominator f) | f<-fracs] :: [(IntMap, IntMap)]
  dmaxes =  M.unionsWith max $ map snd fmaps
  dthresh = M.map (1* toInteger cyclen *) dmaxes
  ifs = (zip [0..] fmaps) :: [(Int, (IntMap, IntMap))]
  opts = optArr fmaps
  eval fs buf n = res where
    state = stateSplit dthresh n
    prev = B.getRange state buf
    looping = isJust prev
    match = (find (compat n . snd) fs) :: Maybe (Int, (IntMap, IntMap))
    res
      | looping = [Step n | leapSteps > 0] ++ Leap leapSteps : nextLoop
      | otherwise = Step n : maybe [] nextFrac match
    (leapSteps, leapState) = leap dmaxes (fromJust prev) state
    nextLoop = eval ifs obuf leapState
    nextFrac (i, f) = eval (opts ! i) (B.insert state buf) $ times n f

cyclesIM :: Int -> [Rational] -> Integer -> [IntMap]
cyclesIM cl f i = [im | Step im <- cs]
    where cs = cycles cl f i
cyclesIM' :: Int -> [Rational] -> IntMap -> [IntMap]
cyclesIM' cl f i = [im | Step im <- cs]
    where cs = cycles' cl f i

mapGetPow k vs = [ v M.! k | v<-filter match vs] where
  match v = M.member k v && (all good $ M.assocs v)
  good (key, p) = if key==k then p>0 else p==0

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
  liveout $ powers 13 $ (:[]) . last $ naive hamming $ 2^(2^k-1)
hammingMain' k = do
  liveout $ mapGetPow 13 $ (:[]) . last $ (cyclesIM' 2) hamming $
    M.fromList [(2, (2^k-1))]

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
  dopg powers naive 20
  putStrLn "Register based with 50 primes:"
  smartpg regBased 50
  putStrLn "Fraction optimized with 50 primes:"
  smartpg fracOpt 50
  putStrLn "Cycle detection with 100 primes:"
  smartpg (cyclesIM 2) 100
  putStrLn "Naive hamming 2^17-1:"
  hammingMain 17
  putStrLn "Cycle hamming 2^2400-1:"
  hammingMain' 2400

demo2 = do
  putStrLn "Naive on 1 fraction input:"
  putStrLn "[takes too long]" -- naiveSelfInterp ftin
  putStrLn "Fraction optimized on 1 fraction input:"
  smartSelfInterp fracOpt' ftin
  putStrLn "Cycle detection on 1 fraction input:"
  smartSelfInterp (cyclesIM' 16) ftin
  putStrLn "Cycle detection on 2 fraction input:"
  smartSelfInterp (cyclesIM' 16) ftin'

main = demo
