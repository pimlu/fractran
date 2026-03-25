module Compiled where

import Data.Array
import Data.Bits ((.&.), (.|.), shiftL)
import Data.List (foldl', nub, sort)
import Data.Ratio
import qualified Data.Map.Strict as M

import Fractran

type ExpVec = Array Int Integer

data CompiledRule = CompiledRule
  { compiledNum :: IntMap
  , compiledDen :: IntMap
  , compiledDenIx :: [(Int, Integer)]
  , compiledReqMask :: Int
  , compiledDelta :: ExpVec
  , compiledNumValue :: Integer
  , compiledDenValue :: Integer
  }

data LutProgram = LutProgram
  { lutRuleIndex :: Array Int Int
  }

data CompiledProgram = CompiledProgram
  { cpPrimes :: Array Int Int
  , cpPrimeIndex :: M.Map Int Int
  , cpRules :: Array Int CompiledRule
  , cpInitialRuleOrder :: [Int]
  , cpRuleOpts :: Array Int [Int]
  , cpLut :: Maybe LutProgram
  }

compileProgram :: [Rational] -> CompiledProgram
compileProgram fracs =
  CompiledProgram
    { cpPrimes = primeArray
    , cpPrimeIndex = primeIndex
    , cpRules = ruleArray
    , cpInitialRuleOrder = ruleIndices
    , cpRuleOpts = ruleOpts
    , cpLut = buildLut primeArray compiledRules
    }
  where
    fmaps = [(facmap $ numerator f, facmap $ denominator f) | f <- fracs]
    primeList =
      sort $
        nub $
          concatMap (\(num, den) -> M.keys num ++ M.keys den) fmaps
    primeArray = listArray (0, length primeList - 1) primeList
    primeIndex = M.fromList $ zip primeList [0 ..]
    compiledRules = map compileRule fmaps
    ruleIndices = [0 .. length compiledRules - 1]
    ruleArray = listArray (0, length compiledRules - 1) compiledRules
    ruleOpts = listArray (bounds ruleArray) [ruleOpt ix | ix <- indices ruleArray]
    compileRule (num, den) =
      CompiledRule
        { compiledNum = num
        , compiledDen = den
        , compiledDenIx =
            [ (primeIndex M.! prime, needed)
            | (prime, needed) <- M.assocs den
            ]
        , compiledReqMask =
            foldl'
              (\mask (prime, needed) ->
                  if needed > 0
                    then mask .|. (1 `shiftL` (primeIndex M.! prime))
                    else mask)
              0
              (M.assocs den)
        , compiledDelta = deltaArray primeArray num den
        , compiledNumValue = unfmap num
        , compiledDenValue = unfmap den
        }
    ruleOpt ix = preOpt ix ++ [ix .. snd (bounds ruleArray)]
    preOpt ix =
      [ preIx
      | preIx <- [0 .. ix - 1]
      , couldPre (compiledNum (ruleArray ! ix)) (compiledDen (ruleArray ! preIx))
      ]
    couldPre num den = not (M.null (M.intersection num den))

deltaArray :: Array Int Int -> IntMap -> IntMap -> ExpVec
deltaArray basis num den = listArray bounds entries
  where
    bounds = boundsOf basis
    entries =
      [ M.findWithDefault 0 prime num - M.findWithDefault 0 prime den
      | (_, prime) <- assocs basis
      ]

boundsOf :: Array Int a -> (Int, Int)
boundsOf = bounds

encodeInteger :: CompiledProgram -> Integer -> ExpVec
encodeInteger program n = encodeIntMap program (facmap n)

encodeIntMap :: CompiledProgram -> IntMap -> ExpVec
encodeIntMap program exponents =
  listArray (bounds basis) $
    [ M.findWithDefault 0 prime exponents
    | (_, prime) <- assocs basis
    ]
  where
    basis = cpPrimes program

decodeExpVec :: CompiledProgram -> ExpVec -> IntMap
decodeExpVec program exponents =
  M.fromList
    [ (prime, pow)
    | (ix, pow) <- assocs exponents
    , pow /= 0
    , let prime = cpPrimes program ! ix
    ]

stepCompiled :: CompiledProgram -> ExpVec -> Maybe ExpVec
stepCompiled program state =
  case firstCompatible (cpInitialRuleOrder program) of
    Just rule -> Just (applyRule state rule)
    Nothing -> Nothing
  where
    rules = cpRules program
    firstCompatible [] = Nothing
    firstCompatible (ruleIx : rest)
      | ruleCompatible state rule = Just rule
      | otherwise = firstCompatible rest
      where
        rule = rules ! ruleIx

stepLut :: CompiledProgram -> ExpVec -> Either String (Maybe ExpVec)
stepLut program state =
  case cpLut program of
    Nothing -> Left "lut incompatible with non-binary denominator thresholds"
    Just lut ->
      let mask = stateMask state
          ruleIx = lutRuleIndex lut ! mask
       in if ruleIx < 0
            then Right Nothing
            else Right $ Just (applyRule state (cpRules program ! ruleIx))

ruleCompatible :: ExpVec -> CompiledRule -> Bool
ruleCompatible state rule = all enough (compiledDenIx rule)
  where
    enough (ix, needed) = state ! ix >= needed

applyRule :: ExpVec -> CompiledRule -> ExpVec
applyRule state rule = listArray (bounds state) (zipWith (+) (elems state) (elems (compiledDelta rule)))
  where
    -- The compiled basis is small in the current workloads, so element-wise
    -- zipping avoids repeated array indexing in the hot path.

runCompiled :: CompiledProgram -> Integer -> [IntMap]
runCompiled program initN = unfold (cpInitialRuleOrder program) (encodeInteger program initN)
  where
    rules = cpRules program
    opts = cpRuleOpts program
    unfold candidateRules state =
      case firstCompatible candidateRules state of
        Just (ruleIx, next) -> decodeExpVec program next : unfold (opts ! ruleIx) next
        Nothing -> []
    firstCompatible [] _ = Nothing
    firstCompatible (ruleIx : rest) state
      | ruleCompatible state rule = Just (ruleIx, applyRule state rule)
      | otherwise = firstCompatible rest state
      where
        rule = rules ! ruleIx

runCompiledExpVec :: CompiledProgram -> Integer -> [ExpVec]
runCompiledExpVec program initN = unfold (cpInitialRuleOrder program) (encodeInteger program initN)
  where
    rules = cpRules program
    opts = cpRuleOpts program
    unfold candidateRules state =
      case firstCompatible candidateRules state of
        Just (ruleIx, next) -> next : unfold (opts ! ruleIx) next
        Nothing -> []
    firstCompatible [] _ = Nothing
    firstCompatible (ruleIx : rest) state
      | ruleCompatible state rule = Just (ruleIx, applyRule state rule)
      | otherwise = firstCompatible rest state
      where
        rule = rules ! ruleIx

runCompiledTrace :: CompiledProgram -> Integer -> [(ExpVec, Integer)]
runCompiledTrace program initN = unfold (cpInitialRuleOrder program) initN (encodeInteger program initN)
  where
    rules = cpRules program
    opts = cpRuleOpts program
    unfold candidateRules currentValue state =
      case firstCompatible candidateRules state of
        Just (ruleIx, next) ->
          let rule = rules ! ruleIx
              nextValue = (currentValue * compiledNumValue rule) `div` compiledDenValue rule
           in (next, nextValue) : unfold (opts ! ruleIx) nextValue next
        Nothing -> []
    firstCompatible [] _ = Nothing
    firstCompatible (ruleIx : rest) state
      | ruleCompatible state rule = Just (ruleIx, applyRule state rule)
      | otherwise = firstCompatible rest state
      where
        rule = rules ! ruleIx

unfExpVec :: CompiledProgram -> ExpVec -> Integer
unfExpVec program exponents =
  foldl'
    (\prod (ix, pow) ->
        if pow == 0
          then prod
          else prod * toInteger (cpPrimes program ! ix) ^ pow)
    1
    (assocs exponents)

expVecStateHash :: CompiledProgram -> ExpVec -> Integer
expVecStateHash program =
  foldl' step 1469598103934665603 . assocs
  where
    step acc (ix, exponent)
      | exponent == 0 = acc
      | otherwise =
          let prime = cpPrimes program ! ix
           in ((acc * 1099511628211) + fromIntegral prime * 1000003 + exponent)

runLut :: CompiledProgram -> Integer -> Either String [IntMap]
runLut program initN =
  case cpLut program of
    Nothing -> Left "lut incompatible with non-binary denominator thresholds"
    Just _ -> Right (unfold (encodeInteger program initN))
  where
    unfold state =
      case stepLut program state of
        Left _ -> []
        Right (Just next) -> decodeExpVec program next : unfold next
        Right Nothing -> []

lutCompatible :: CompiledProgram -> Bool
lutCompatible = maybe False (const True) . cpLut

buildLut :: Array Int Int -> [CompiledRule] -> Maybe LutProgram
buildLut primeArray rules
  | any hasThresholdGtOne rules = Nothing
  | primeCount > finiteBitBudget = Nothing
  | otherwise = Just $ LutProgram {lutRuleIndex = table}
  where
    primeCount = rangeSize (bounds primeArray)
    finiteBitBudget = 20
    tableBounds = (0, (1 `shiftL` primeCount) - 1)
    table = listArray tableBounds [firstApplicable mask | mask <- range tableBounds]
    hasThresholdGtOne rule = any (\(_, needed) -> needed > 1) (compiledDenIx rule)
    firstApplicable mask = go 0 rules
      where
        go _ [] = -1
        go ix (rule : rest)
          | ruleReqSatisfied mask rule = ix
          | otherwise = go (ix + 1) rest

ruleReqSatisfied :: Int -> CompiledRule -> Bool
ruleReqSatisfied mask rule = (mask .&. compiledReqMask rule) == compiledReqMask rule

stateMask :: ExpVec -> Int
stateMask state =
  foldl'
    (\mask ix -> if state ! ix > 0 then mask .|. (1 `shiftL` ix) else mask)
    0
    (indices state)
