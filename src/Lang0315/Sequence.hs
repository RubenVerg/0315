module Lang0315.Sequence
( Sequence(..)
, seqDivMod
, seqDiv
, seqMod
, seqPow
, seqBoolean
, seqIndex
, seqUnTriangle
, seqUnSquare
, seqKeep
, seqCut
, seqJoin
, seqCharacter
, byAntiDiagonals
) where


import Data.Bifunctor (bimap)
import Data.List (genericIndex, genericReplicate, genericLength)
import Data.Maybe (isNothing, isJust, catMaybes)
import Data.Universe.Helpers (diagonals)

newtype Sequence = Sequence { unSequence :: [Integer] }

instance Num Sequence where
  (Sequence xs) + (Sequence ys) = Sequence $ zipWith (+) xs ys
  (Sequence xs) - (Sequence ys) = Sequence $ zipWith (-) xs ys
  (Sequence xs) * (Sequence ys) = Sequence $ zipWith (*) xs ys
  negate (Sequence xs) = Sequence $ map negate xs
  abs (Sequence xs) = Sequence $ map abs xs
  signum (Sequence xs) = Sequence $ map signum xs
  fromInteger = error "Cannot convert number into sequence"

seqDivMod :: Sequence -> Sequence -> (Sequence, Sequence)
seqDivMod (Sequence xs) (Sequence ys) = bimap Sequence Sequence $ unzip $ zipWith divMod xs ys

seqDiv :: Sequence -> Sequence -> Sequence
seqDiv (Sequence xs) (Sequence ys) = Sequence $ zipWith div xs ys

seqMod :: Sequence -> Sequence -> Sequence
seqMod (Sequence xs) (Sequence ys) = Sequence $ zipWith mod xs ys

seqPow :: Sequence -> Sequence -> Sequence
seqPow (Sequence xs) (Sequence ys) = Sequence $ zipWith (\x y -> if y < 0 then 0 else x ^ y) xs ys

fromBoolean :: Bool -> Integer
fromBoolean True = 1
fromBoolean False = 0

seqBoolean :: (Integer -> Integer -> Bool) -> Sequence -> Sequence -> Sequence
seqBoolean f (Sequence xs) (Sequence ys) = Sequence $ zipWith (\x y -> fromBoolean $ f x y) xs ys

seqIndex :: Sequence -> Sequence -> Sequence
seqIndex (Sequence xs) (Sequence is) = Sequence $ map (\i -> if i < 0 then 0 else xs `genericIndex` i) is

seqUnTriangle :: Sequence -> Sequence -> Sequence
-- seqUnTriangle (Sequence is) (Sequence js) = Sequence $ catMaybes $ zipWith unTriIndex is js
seqUnTriangle (Sequence is) (Sequence js) = Sequence $ concatMap (\i -> catMaybes $ takeWhile isJust $ dropWhile isNothing $ map (unTriIndex i) js) is where
  unTriIndex i j | i < 0 = Nothing
                 | j < 0 || j > i = Nothing
                 | otherwise = Just $ i * (i + 1) `div` 2 + j

byAntiDiagonals :: (a -> b -> c) -> [a] -> [b] -> [c]
byAntiDiagonals f xs ys = concat $ diagonals [[f x y | y <- ys] | x <- xs]

seqUnSquare :: Sequence -> Sequence -> Sequence
seqUnSquare (Sequence is) (Sequence js) = Sequence $ catMaybes $ byAntiDiagonals unSqIndex is js where
  unSqIndex i j | i < 0 = Nothing
                | otherwise = Just $ (i + j) * (i + j + 1) `div` 2 + j

seqCharacter :: Sequence -> Sequence
seqCharacter (Sequence xs) = Sequence $ flip map [0..] $ \n -> genericLength $ takeWhile (== n) $ dropWhile (< n) xs

seqKeep :: Sequence -> Sequence -> Sequence
seqKeep (Sequence xs) (Sequence cs) = Sequence $ concat $ zipWith genericReplicate cs xs

seqCut :: Sequence -> Sequence
seqCut (Sequence xs) = Sequence $ takeWhile (/= 0) xs

seqJoin :: Sequence -> Sequence -> Sequence
seqJoin (Sequence xs) (Sequence ys) = Sequence $ xs ++ ys
