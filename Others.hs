module Others where
--Has suboptimal implementations for benchmarking

import Data.Ratio
import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Fractran

naive :: [Rational] -> Integer -> [Integer]
naive fs n = maybe [] (next . numerator) match where
  ps = map (*fromIntegral n) fs
  match = find ((==1) . denominator) ps
  next p = p : naive fs p
--bit faster, bit uglier
naive' :: [Rational] -> Integer -> [Integer]
naive' fs n = maybe [] (next . prod) match where
  rats = [(numerator f, denominator f) | f <- fs]
  match = find (\(num, den) -> (n*num) `rem` den == 0) rats
  prod (num, den) = (n*num) `div` den
  next p = p : naive' fs p

--register based, no fraction optimization
regBased :: [Rational] -> Integer -> [IntMap]
regBased fracs init = regBased' fracs $ facmap init
regBased' fracs init = eval init where
  fs = [(facmap $ numerator f, facmap $ denominator f) | f<-fracs]
  match n = find (compat n) fs
  eval n = maybe [] (next . times n) $ match n
  next p = p : eval p

--Original 4x (more?) slower times implementation
timesBad :: IntMap -> (IntMap, IntMap) -> IntMap
timesBad x (num, den) = M.fromList pairs where
  keys = S.toList $ S.fromList $ M.keys x ++ M.keys num ++ M.keys den
  pairs = [(k, get0 k x + get0 k num - get0 k den) | k<-keys]