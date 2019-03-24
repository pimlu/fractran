{-# LANGUAGE BangPatterns #-}
module Fractran where

import Data.Ratio
import Data.Maybe
import Data.List
import GHC.Exts
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Array
import Control.Exception
import qualified Data.Sequence as Q

import qualified CBuf as B

type IntMap = M.Map Int Integer
data CycleStep = Step IntMap | Leap Integer deriving (Eq, Show)

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

primes :: [Integer]
primes = eratos [2..] where
  eratos []     = []
  eratos (p:xs) = p : eratos (xs `minus` [p*p, p*p+p..])
factors :: Integer -> [Integer]
factors n = fac primes n where
  fac _ 1 = []
  fac (p:ps) k
    | k `rem` p == 0 = p : fac (p:ps) (k `div` p)
    | otherwise = fac ps k

isPrime :: Integer -> Bool
isPrime n = head (dropWhile (< n) primes) == n

validateIM :: IntMap -> IntMap
validateIM im = maybe im throw comp where
  comp = find (not . isPrime . fromIntegral) $ M.keys im
  throw c = error $ show c ++ " is not a real prime factor in the input."


times :: IntMap -> (IntMap, IntMap) -> IntMap
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

optArr :: [(IntMap, IntMap)] -> Array Int [(Int, (IntMap, IntMap))]
optArr fs = listArray (0, length fs - 1) opts where
  ifs = zip [0..] fs
  opts = [opt i f | (i,f) <- ifs]
  opt i f = let (pre,post) = splitAt i ifs in (preOpt f pre ++ post)
  preOpt (num, _) pre = (filter (couldPre num . snd . snd) pre)
  couldPre a b = not . M.null $ M.intersection a b
  msg = unlines $ [show (i, map fst o) | (i,o)<-zip [0..] opts]

fracOpt :: [Rational] -> Integer -> [IntMap]
fracOpt fracs init = fracOpt' fracs $ facmap init
fracOpt' fracs init = eval ifs $ validateIM init where
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
      rem = sk + dip - (get0 k dmaxes)
      diff = get0 k diffs
  (steps, newdata) = case cs of
    [] -> error ("Nonterminating cycle detected, state: "++show (fprod pdata plogic)++
      ".  This means the program entered an infinite loop.")
    _ -> let s = minimum cs in
        (fromIntegral len * s - 1,
        fprod sdata $ M.map (* (-s)) diffs)
  n = fprod slogic newdata

cycles :: Int -> [Rational] -> Integer -> [CycleStep]
cycles cyclen fracs init = cycles' cyclen fracs $ facmap init
cycles' :: Int -> [Rational] -> IntMap -> [CycleStep]
cycles' cyclen fracs init = tail $ eval ifs obuf $ validateIM init where
  obuf = (B.cbuf cyclen snd []) :: B.CBuf (IntMap, IntMap) IntMap
  fmaps = [(facmap $ numerator f, facmap $ denominator f) | f<-fracs] :: [(IntMap, IntMap)]
  dmaxes =  M.unionsWith max $ map snd fmaps
  dthresh = M.map (1* toInteger cyclen *) dmaxes
  ifs = (zip [0..] fmaps) :: [(Int, (IntMap, IntMap))]
  opts = optArr fmaps
  eval fs buf n = Step n : next where
    state = stateSplit dthresh n
    prev = B.getRange state buf
    looping = isJust prev
    match = (find (compat n . snd) fs) :: Maybe (Int, (IntMap, IntMap))
    next
      | looping && leapSteps <= 0 = nextLoop
      | looping = Leap leapSteps : nextLoop
      | otherwise = maybe [] nextFrac match
    (leapSteps, leapState) = leap dmaxes (fromJust prev) state
    nextLoop = eval ifs obuf leapState
    nextFrac (i, f) = eval (opts ! i) (B.insert state buf) $ times n f

stepCount :: [CycleStep] -> [(Integer, IntMap)]
stepCount cs = [(count, im) | (count, Just im) <- scs] where
  scs = scanl reduce (0, Nothing) cs
  reduce (!count, _) (Step im) = (count+1, Just im)
  reduce (!count, _) (Leap k) = (count+k, Nothing)

mapGetPow k vs = [ v M.! k | v<-filter match vs] where
  match v = M.member k v && (all good $ M.assocs v)
  good (key, p) = if key==k then p>0 else p==0
