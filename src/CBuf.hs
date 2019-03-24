{-# LANGUAGE ViewPatterns, PatternSynonyms #-}
module CBuf where


import qualified Data.Set as S
import qualified Data.Sequence as Q
import Data.Foldable
import Data.Maybe
import Control.Exception

data CBuf a b = CBuf Int (Q.Seq a) (S.Set b) (a -> b)

instance (Show a, Show b) => Show (CBuf a b) where
  show (CBuf n seq set _) = unwords [show n, show seq, show set]

-- Constructs a circular buffer.
-- Can test for similarity using [has] based on [fn], which should
-- return unique values for each inserted input.
cbuf :: (Ord b) => Int -> (a -> b) -> [a] -> CBuf a b
cbuf n fn input = assert (length set == length s) cb where
  set = S.fromList s
  l = take n input
  s = map fn l
  cb = CBuf n (Q.fromList l) set fn

getSet (CBuf _ _ set _) = set
getSeq (CBuf _ seq _ _) = seq

-- Inserts a value into the circular buffer.
-- Most of the time you have a duty to call [has]
-- before [insert] to find duplicates.
insert ::  (Ord b) => a -> CBuf a b -> CBuf a b
insert v cb = assert (not $ elem (fn v) set) $ insert' v cb where
  (CBuf _ _ set fn) = cb

insert' ::  (Ord b) => a -> CBuf a b -> CBuf a b
insert' v cb
  | bufLen cb >= cycLen cb = cycInsert v cb
  | otherwise = lowInsert v cb
bufLen :: CBuf a b -> Int
bufLen (CBuf _ seq _ _) = Q.length seq
cycLen :: CBuf a b -> Int
cycLen (CBuf n _ _ _) = n

cycInsert ::  (Ord b) => a -> CBuf a b -> CBuf a b
cycInsert v (CBuf n seq set fn) = CBuf n nseq nset fn where
  nseq = v Q.<| (Q.take last seq)
  nset = S.insert (fn v) $ S.delete (fn $ Q.index seq last) set
  last = Q.length seq - 1

lowInsert ::  (Ord b) => a -> CBuf a b -> CBuf a b
lowInsert v (CBuf n seq set fn) = CBuf n nseq nset fn where
  nseq = v Q.<| seq
  nset = S.insert (fn v) set

-- Tests for containment of [fn v]. Usually called before [insert]
has :: (Ord b) => a -> CBuf a b -> Bool
has v (CBuf _ _ set fn) = S.member (fn v) set
-- Tests for containment of [fn v]. Usually called before [insert]
get :: (Ord b) => a -> CBuf a b -> Maybe a
get v (CBuf _ seq set fn) = if S.member fv set
    then match
    else Nothing where
  fv = fn v
  match = find ((==fv) . fn) seq

getRange :: (Ord b) => a -> CBuf a b -> Maybe (Q.Seq a)
getRange v (CBuf _ seq set fn) = if S.member fv set
    then (match :: Maybe Int) >>= (\m -> Just $ Q.take (m+1) seq)
    else Nothing where
  fv = fn v
  match = Q.findIndexL ((==fv) . fn) seq
