{-# LANGUAGE PatternSynonyms, ViewPatterns #-}

module Lang0315.Sequence
( pattern (:>)
, Sequence(..)
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
, a000012
, a001477
, a000027
, a000040
, a000045
, a000203
, a000005
, a000217
, a000010
, a000108
, a000041
, a000290
, a001222
, a000142
, a001221
, a000720
, a007318
, a000120
, a005117
, a002110
, a001622
, a001358
, a008683
, a000032
, a000225
, a000110
, a005408
, a002275
, a006530
, a000007
, a000796
, a000961
, a000984
, a000578
, a002808
, a020639
, a000244
, a070939
, a000292
, a002113
, a000129
, a005843
, a000035
, a001045
, a001113
, a000396
, a000043
, a001764
, a001147
, a008277
, a000312
, a000302
, a000670
, a001006
, a010060
, a001065
, a055642
, a000079
, a100995
, a014963
, a023443
, a000326
, a000166
, a000330
, a002620
, a001511
, a004526
, a000085
, a001227
, a001906
, a000124
, a001405
, a000583
, a018252
, a001157
, a001700
, a008292
, a005101
, a001615
, a003418
, a000169
, a246655
, a027641
, a027642
, a000272
, a000004
, a000204
, a000069
, a002322
, a001969
, a000002
, a003056
, a000593
, a001097
, a006882
, a011557
, a000262
, a005811
, a144944
, a001003
, a000196
, a001481
, a005100
, a001037
, a000594
, a000688
, a000001
, a000031
, a000058
, a008279
, a001057
, a000161
, a001489
, a001478
, a022958
, a022996
, a109613
, a008585
, a069074
, a010709
, a059841
, a000034
, a033999
, a010684
, a010685
, a010673
, a010674
, a010688
, a105397
, a049347
, a011655
, a061347
, a102283
, a130196
, a131534
, a010882
, a153727
, a080425
, a144437
, a131713
, a130784
, a169609
, a131561
, a052901
, a274339
, a073636
, a101000
, a131598
, a177702
, a131756
, a132677
, a146325
, a173259
, a164360
, a079978
, a000009
, a000726
, a001935
, a035959
, a219601
, a035985
, a261775
, a104502
, a261776
, a328545
, a328546
, a001970
, a034691
, a034899
, a166861
, a000335
, a005928
, a073592
, a061256
, a061255
, a000332
, a000391
, a005043
, a061257
, a000389
, a000417
, a000579
, a000428
, a107895
, a030009
, a092119
, a051064
, a173241
, a261031
, a030012
) where

import Control.Monad ((>=>))
import Data.Bifunctor (bimap)
import Data.List (genericIndex, genericReplicate, genericLength, sort, sortOn, group, unsnoc, inits)
import Data.Ord (Down(..))
import Data.Maybe (isNothing, isJust, catMaybes, fromMaybe)
import Data.Ratio
import Data.Universe.Helpers (diagonals)

import Data.Bits (popCount)
import Data.Bits.Bitwise (toListLE)
import Math.NumberTheory.Primes (nextPrime, primes, unPrime, factorise, isPrime, UniqueFactorisation)
import Math.NumberTheory.Primes.Counting (primeCount, nthPrime)
import qualified Math.NumberTheory.ArithmeticFunctions as AF
import qualified Math.NumberTheory.Recurrences as Rec
import Data.Number.CReal (CReal, showCReal)

import qualified Data.List.Infinite as IL

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
seqCharacter (Sequence xs) = Sequence $ ofIndices $ \n -> genericLength $ takeWhile (== n) $ dropWhile (< n) xs

seqKeep :: Sequence -> Sequence -> Sequence
seqKeep (Sequence xs) (Sequence cs) = Sequence $ concat $ zipWith genericReplicate cs xs

seqCut :: Sequence -> Sequence
seqCut (Sequence xs) = Sequence $ takeWhile (/= 0) xs

seqJoin :: Sequence -> Sequence -> Sequence
seqJoin (Sequence xs) (Sequence ys) = Sequence $ xs ++ ys

ofIndices :: (Integer -> a) -> [a]
ofIndices f = map f $ enumFrom 0

ofPositive :: (Integer -> a) -> [a]
ofPositive f = map f $ enumFrom 1

binomial :: Integer -> Integer -> Integer
binomial n k = fromMaybe 0 $ Rec.binomialLine n `maybeIndex` k

stirling2 :: Integer -> Integer -> Integer
stirling2 n k = Rec.stirling2 `infiniteIndex` n `genericIndex` k

superCatalanT :: [[Integer]]
superCatalanT = iterate f [1] where f us = vs ++ [last vs] where vs = scanl1 (+) $ zipWith (+) us $ 0 : us

superCatalan :: Integer -> Integer -> Integer
superCatalan n k = superCatalanT `genericIndex` n `genericIndex` k

infiniteIndex :: IL.Infinite a -> Integer -> a
infiniteIndex xs i | i < 0 = error "Negative index!"
                   | otherwise = IL.foldr (\x acc m -> if m == 0 then x else acc (m - 1)) xs i

maybeIndex :: [a] -> Integer -> Maybe a
maybeIndex _ i | i < 0 = Nothing
maybeIndex [] _ = Nothing
maybeIndex (x:_) 0 = Just x
maybeIndex (_:xs) i = maybeIndex xs $ i - 1

reverseDigits :: Integer -> Integer
reverseDigits x | x >= 0 = read $ reverse $ show x
                | otherwise = negate $ read $ reverse $ show $ negate x

adicValuation :: Integer -> Integer -> Integer
adicValuation = loop 0 where
  loop count _ 0 = count
  loop count p n = case n `divMod` p of
    (n', 0) -> loop (count + 1) p n'
    _ -> count

dedekindPsiHelperA :: Integral n => AF.ArithmeticFunction n (Ratio n)
dedekindPsiHelperA = AF.multiplicative (\p _ -> 1 + 1 % unPrime p)

dedekindPsi :: (UniqueFactorisation n, Integral n) => n -> n
dedekindPsi n = numerator $ n % 1 * AF.runFunction dedekindPsiHelperA n

intSquareRoots :: [Integer]
intSquareRoots = concat $ zipWith genericReplicate [1 :: Integer, 3..] [0..]

intSquareRoot :: Integer -> Integer
intSquareRoot n | n < 0 = 0
                | otherwise = intSquareRoots `genericIndex` n

isSquare :: Integer -> Bool
isSquare n = let r = intSquareRoot n in r * r == n

maximumAmountOfDigits :: Int
maximumAmountOfDigits = 1024

digitSequence :: CReal -> [Integer]
digitSequence = showCReal maximumAmountOfDigits >=> (\case
  '0' -> [0]
  '1' -> [1]
  '2' -> [2]
  '3' -> [3]
  '4' -> [4]
  '5' -> [5]
  '6' -> [6]
  '7' -> [7]
  '8' -> [8]
  '9' -> [9]
  _ -> [])

realPhi :: CReal
realPhi = (1 + sqrt 5) / 2

{-# COMPLETE [], (:>) #-}
infixl 5 :>
pattern (:>) :: [a] -> a -> [a]
pattern xs :> x <- (unsnoc -> Just (xs, x))
  where xs :> x = xs ++ [x]

eulerTransform' :: [Integer] -> [Integer]
eulerTransform' as = bs where
  cs = map (sum . map (\d -> d * as `genericIndex` (d - 1)) . AF.divisorsList) [1..]
  bs = zipWith f [1..] $ map reverse $ drop 1 $ inits cs
  f n (cn : ci) = (cn + sum (zipWith (*) bs ci)) `div` n
  f _ _ = error "Unreachable"

eulerTransform :: [Integer] -> [Integer]
eulerTransform = (1:) . eulerTransform'

{-
inverseEulerTransform :: [Integer] -> [Integer]
inverseEulerTransform bs = as where
  cs = zipWith f [1..] $ map reverse $ drop 1 $ inits bs
  f n (bn : bi) = n * bn - sum (zipWith (*) cs bi)
  f _ _ = error "Unreachable"
  as = map (\n -> flip div n $ sum $ map (\(d :: Integer) -> traceWith (show . take 10) cs `genericIndex` (d - 1) * AF.runMoebius (AF.moebius $ n `div` d)) $ AF.divisorsList n) [1..]
-}

-- See LICENSE.OEIS
-- https://oeis.org/
a000012, a001477, a000027, a000040, a000045, a000203, a000005, a000217, a000010, a000108 :: Sequence
a000041, a000290, a001222, a000142, a001221, a000720, a007318, a000120, a005117, a002110 :: Sequence
a001622, a001358, a008683, a000032, a000225, a000110, a005408, a002275, a006530, a000007 :: Sequence
a000796, a000961, a000984, a000578, a002808, a020639, a000244, a070939, a000292, a002113 :: Sequence
a000129, a005843, a000035, a001045, a001113, a000396, a000043, a001764, a001147, a008277 :: Sequence
a000312, a000302, a000670, a001006, a010060, a001065, a055642, a000079, a100995, a014963 :: Sequence
a023443, a000326, a000166, a000330, a002620, a001511, a004526, a000085, a001227, a001906 :: Sequence
a000124, a001405, a000583, a018252, a001157, a001700, a008292, a005101, a001615, a003418 :: Sequence
a000169, a246655, a027641, a027642, a000272, a000004, a000204, a000069, a002322, a001969 :: Sequence
a000002, a003056, a000593, a001097, a006882, a011557, a000262, a005811, a144944, a001003 :: Sequence
a000196, a001481, a005100, a001037, a000594, a000688, a000001, a000031, a000058, a008279 :: Sequence
a001057, a000161, a001489, a001478, a022958, a022996, a109613, a008585, a069074, a010709 :: Sequence
a059841, a000034, a033999, a010684, a010685, a010673, a010674, a010688, a105397, a049347 :: Sequence
a011655, a061347, a102283, a130196, a131534, a010882, a153727, a080425, a144437, a131713 :: Sequence
a130784, a169609, a131561, a052901, a274339, a073636, a101000, a131598, a177702, a131756 :: Sequence
a132677, a146325, a173259, a164360, a079978, a000009, a000726, a001935, a035959, a219601 :: Sequence
a035985, a261775, a104502, a261776, a328545, a328546, a001970, a034691, a034899, a166861 :: Sequence
a000335, a005928, a073592, a061256, a061255, a000332, a000391, a005043, a061257, a000389 :: Sequence
a000417, a000579, a000428, a107895, a030009, a092119, a051064, a173241, a261031, a030012 :: Sequence
a000012 = Sequence $ repeat 1
a001477 = Sequence $ enumFrom 0
a000027 = Sequence $ enumFrom 1
a000040 = Sequence $ map unPrime primes
a000045 = Sequence fibonacci where fibonacci = 0 : 1 : zipWith (+) fibonacci (drop 1 fibonacci)
a000203 = Sequence $ ofPositive $ AF.sigma 1
a000005 = Sequence $ ofPositive AF.tau
a000217 = Sequence $ ofIndices $ \n -> n * (n + 1) `div` 2
a000010 = Sequence $ ofPositive AF.totient
a000108 = Sequence $ ofIndices $ \n -> binomial (2 * n) n `div` (n + 1)
a000041 = Sequence $ IL.toList Rec.partition
a000290 = Sequence $ ofIndices $ \n -> n * n
a001222 = Sequence $ ofPositive $ fromIntegral . AF.bigOmega
a000142 = Sequence $ ofIndices $ infiniteIndex Rec.factorial
a001221 = Sequence $ ofPositive AF.smallOmega
a000720 = Sequence $ ofPositive primeCount
a007318 = Sequence $ concat $ IL.toList Rec.binomial
a000120 = Sequence $ ofIndices $ fromIntegral . popCount
a005117 = Sequence $ ofIndices $ genericIndex $ AF.nFrees 2
a002110 = Sequence $ ofIndices $ \case
  0 -> 1
  n -> product $ map unPrime [nextPrime 1..nthPrime (fromEnum n)]
a001622 = Sequence $ digitSequence realPhi
a001358 = Sequence $ filter (\n -> AF.bigOmega n == 2) $ enumFrom 1
a008683 = Sequence $ ofPositive $ \n -> case AF.moebius n of
  AF.MoebiusN -> -1
  AF.MoebiusZ -> 0
  AF.MoebiusP -> 1
a000032 = Sequence lucas where lucas = 2 : 1 : zipWith (+) lucas (drop 1 lucas)
a000225 = Sequence $ map (subtract 1) $ iterate (* 2) 1
a000110 = Sequence $ ofIndices $ \n -> sum $ map (stirling2 n) [0..n]
a005408 = Sequence $ ofIndices $ \n -> 2 * n + 1
a002275 = Sequence $ ofIndices $ \n -> (10 ^ n - 1) `div` 9
a006530 = Sequence $ ofPositive $ \n -> case sortOn Down $ factorise n of
  [] -> 1
  ((p, _):_) -> unPrime p
a000007 = Sequence $ 1 : repeat 0
a000796 = Sequence $ digitSequence pi
a000961 = Sequence $ filter (\n -> AF.smallOmega n <= (1 :: Integer)) $ enumFrom 1
a000984 = Sequence $ ofIndices $ \n -> binomial (2 * n) n
a000578 = Sequence $ ofIndices $ \n -> n * n * n
a002808 = Sequence $ filter (isNothing . isPrime) $ enumFrom 2 -- 1 is not part of the sequence
a020639 = Sequence $ ofPositive $ \n -> case sort $ factorise n of
  [] -> 1
  ((p, _):_) -> unPrime p
a000244 = Sequence $ iterate (* 3) 1
a070939 = Sequence $ 1 : 1 : chunk [1] where chunk xs = let rs = map (+ 1) (xs ++ xs) in rs ++ chunk rs
a000292 = Sequence $ ofIndices $ \n -> n * (n + 1) * (n + 2) `div` 6
a002113 = Sequence $ filter ((==) <*> reverseDigits) $ enumFrom 0
a000129 = Sequence pell where pell = 0 : 1 : zipWith (+) pell (map (2 *) $ drop 1 pell)
a005843 = Sequence $ ofIndices $ \n -> 2 * n
a000035 = Sequence $ cycle [0, 1]
a001045 = Sequence jacobsthal where jacobsthal = 0 : 1 : zipWith (+) (map (2 *) jacobsthal) (drop 1 jacobsthal)
a001113 = Sequence $ digitSequence $ exp 1
a000396 = Sequence $ known ++ filter (\n -> AF.sigma 1 n == 2 * n) (enumFrom $ 1 + maximum known) where
  known = [6, 28, 496, 8128, 33550336, 8589869056, 137438691328, 2305843008139952128, 2658455991569831744654692615953842176, 191561942608236107294793378084303638130997321548169216, 13164036458569648337239753460458722910223472318386943117783728128]
a000043 = Sequence $ filter (\n -> isJust $ isPrime $ (2 :: Integer) ^ n - 1) $ enumFrom 1
a001764 = Sequence $ ofIndices $ \n -> binomial (3 * n) n `div` (2 * n + 1)
a001147 = Sequence $ scanl (\acc n -> acc * (2 * n + 1)) 1 $ enumFrom 0
a008277 = Sequence $ concatMap (drop 1) (IL.toList Rec.stirling2)
a000312 = Sequence $ ofIndices $ \n -> n ^ n
a000302 = Sequence $ scanl (*) 1 $ repeat 4
a000670 = Sequence $ ofIndices $ \n -> sum $ map (\k -> stirling2 n k * Rec.factorial `infiniteIndex` k) [0..n]
a001006 = Sequence $ ofIndices $ \n -> sum $ map (\k -> (binomial (2 * k) k `div` (k + 1)) * binomial n (2 * k)) [0..n `div` 2]
a010060 = Sequence $ ofIndices $ (`mod` 2) . fromIntegral . popCount
a001065 = Sequence $ ofPositive $ \n -> AF.sigma 1 n - n
a055642 = Sequence $ ofIndices $ let go count m = if m >= 10 then go (count + 1) (m `div` 10) else count in go 1
a000079 = Sequence $ scanl (*) 1 $ repeat 2
a100995 = Sequence $ ofPositive $ \n -> case factorise n of
  [(_, e)] -> fromIntegral e
  _ -> 0
a014963 = Sequence $ ofPositive $ \n -> case factorise n of
  [(p, _)] -> unPrime p
  _ -> 1
a023443 = Sequence $ enumFrom $ negate 1
a000326 = Sequence $ ofIndices $ \n -> n * (3 * n - 1) `div` 2
a000166 = Sequence subfact where subfact = 1 : 0 : zipWith (*) [1..] (zipWith (+) subfact $ drop 1 subfact)
a000330 = Sequence $ ofIndices $ \n -> n * (n + 1) * (2 * n + 1) `div` 6
a002620 = Sequence $ ofIndices $ \n -> n * n `div` 4
a001511 = Sequence $ ofPositive $ \n -> adicValuation 2 $ n * 2
a004526 = Sequence $ ofIndices $ \n -> n `div` 2
a000085 = Sequence involutions where involutions = 1 : 1 : zipWith (+) (zipWith (*) [1..] involutions) (drop 1 involutions)
a001227 = Sequence $ ofPositive $ \n -> AF.tau n `div` (adicValuation 2 n + 1)
a001906 = Sequence evenFibonacci where evenFibonacci = 0 : 1 : zipWith subtract evenFibonacci (map (* 3) $ drop 1 evenFibonacci)
a000124 = Sequence $ ofIndices $ \n -> n * (n + 1) `div` 2 + 1
a001405 = Sequence $ ofIndices $ \n -> binomial n (n `div` 2)
a000583 = Sequence $ ofIndices $ \n -> n * n * n * n
a018252 = Sequence $ filter (isNothing . isPrime) $ enumFrom 1
a001157 = Sequence $ ofPositive $ AF.sigma 2
a001700 = Sequence $ ofIndices $ \n -> binomial (2 * n + 1) (n + 1)
a008292 = Sequence $ concat $ IL.toList Rec.eulerian1
a005101 = Sequence $ filter (\n -> AF.sigma 1 n > 2 * n) $ enumFrom 1
a001615 = Sequence $ ofPositive dedekindPsi
a003418 = Sequence $ ofIndices $ \n -> foldl lcm 1 [1..n]
a000169 = Sequence $ ofPositive $ \n -> n ^ (n - 1)
a246655 = Sequence $ filter (\n -> AF.smallOmega n <= (1 :: Integer)) $ enumFrom 1
a027641 = Sequence $ map numerator $ IL.toList Rec.bernoulli
a027642 = Sequence $ map denominator $ IL.toList Rec.bernoulli
a000272 = Sequence $ 1 : 1 : map (\n -> n ^ (n - 2)) (enumFrom 2)
a000004 = Sequence $ repeat 0
a000204 = Sequence lucas' where lucas' = 1 : 3 : zipWith (+) lucas' (drop 1 lucas')
a000069 = Sequence $ filter (odd . popCount) $ enumFrom 0
a002322 = Sequence $ ofPositive AF.carmichael
a001969 = Sequence $ filter (even . popCount) $ enumFrom 0
a000002 = Sequence kolakoski where kolakoski = 1 : 2 : drop 2 (concat $ zipWith genericReplicate kolakoski $ cycle [1, 2])
a003056 = Sequence $ byAntiDiagonals (+) (enumFrom 0) (enumFrom 0)
a000593 = Sequence $ ofPositive $ \n -> AF.sigma 1 n - if even n then 2 * AF.sigma 1 (n `div` 2) else 0
a001097 = Sequence $ map unPrime $ filter (\p -> let p' = unPrime p in unPrime (pred p) == p' - 2 || unPrime (succ p) == p' + 2) $ drop 1 primes
a006882 = Sequence df where df = 1 : 1 : zipWith (*) [2..] df
a011557 = Sequence $ scanl (*) 1 $ repeat 10
a000262 = Sequence sol where sol = 1 : 1 : zipWith subtract (zipWith (*) [1..] $ zipWith (*) [0..] sol) (zipWith (*) [3, 5..] $ drop 1 sol)
a005811 = Sequence $ 0 : ofPositive (genericLength . group . toListLE)
a144944 = Sequence $ concat superCatalanT
a001003 = Sequence $ ofIndices $ \n -> superCatalan n n
a000196 = Sequence intSquareRoots
a001481 = Sequence $ filter (\n -> any isSquare [n - k * k | k <- [0..intSquareRoot n]]) $ enumFrom 0
a005100 = Sequence $ filter (\n -> AF.sigma 1 n < 2 * n) $ enumFrom 1
a001037 = Sequence $ 1 : ofPositive (\n -> (`div` n) $ sum $ map (\d -> AF.runMoebius (AF.moebius $ n `div` d) * 2 ^ d) $ AF.divisorsList n)
a000594 = Sequence $ ofPositive AF.ramanujan
a000688 = Sequence $ ofPositive $ AF.runFunction $ AF.multiplicative (\_ k -> Rec.partition `infiniteIndex` fromIntegral k)
a000001 = Sequence [0, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5, 1, 2, 1, 14, 1, 5, 1, 5, 2, 2, 1, 15, 2, 2, 5, 4, 1, 4, 1, 51, 1, 2, 1, 14, 1, 2, 2, 14, 1, 6, 1, 4, 2, 2, 1, 52, 2, 5, 1, 5, 1, 15, 2, 13, 2, 2, 1, 13, 1, 2, 4, 267, 1, 4, 1, 5, 1, 4, 1, 50, 1, 2, 3, 4, 1, 6, 1, 52, 15, 2, 1, 15, 1, 2, 1, 12, 1, 10, 1, 4, 2, 2, 1, 231, 1, 5, 2, 16, 1, 4, 1, 14, 2, 2, 1, 45, 1, 6, 2, 43, 1, 6, 1, 5, 4, 2, 1, 47, 2, 2, 1, 4, 5, 16, 1, 2328, 2, 4, 1, 10, 1, 2, 5, 15, 1, 4, 1, 11, 1, 2, 1, 197, 1, 2, 6, 5, 1, 13, 1, 12, 2, 4, 2, 18, 1, 2, 1, 238, 1, 55, 1, 5, 2, 2, 1, 57, 2, 4, 5, 4, 1, 4, 2, 42, 1, 2, 1, 37, 1, 4, 2, 12, 1, 6, 1, 4, 13, 4, 1, 1543, 1, 2, 2, 12, 1, 10, 1, 52, 2, 2, 2, 12, 2, 2, 2, 51, 1, 12, 1, 5, 1, 2, 1, 177, 1, 2, 2, 15, 1, 6, 1, 197, 6, 2, 1, 15, 1, 4, 2, 14, 1, 16, 1, 4, 2, 4, 1, 208, 1, 5, 67, 5, 2, 4, 1, 12, 1, 15, 1, 46, 2, 2, 1, 56092, 1, 6, 1, 15, 2, 2, 1, 39, 1, 4, 1, 4, 1, 30, 1, 54, 5, 2, 4, 10, 1, 2, 4, 40, 1, 4, 1, 4, 2, 4, 1, 1045, 2, 4, 2, 5, 1, 23, 1, 14, 5, 2, 1, 49, 2, 2, 1, 42, 2, 10, 1, 9, 2, 6, 1, 61, 1, 2, 4, 4, 1, 4, 1, 1640, 1, 4, 1, 176, 2, 2, 2, 15, 1, 12, 1, 4, 5, 2, 1, 228, 1, 5, 1, 15, 1, 18, 5, 12, 1, 2, 1, 12, 1, 10, 14, 195, 1, 4, 2, 5, 2, 2, 1, 162, 2, 2, 3, 11, 1, 6, 1, 42, 2, 4, 1, 15, 1, 4, 7, 12, 1, 60, 1, 11, 2, 2, 1, 20169, 2, 2, 4, 5, 1, 12, 1, 44, 1, 2, 1, 30, 1, 2, 5, 221, 1, 6, 1, 5, 16, 6, 1, 46, 1, 6, 1, 4, 1, 10, 1, 235, 2, 4, 1, 41, 1, 2, 2, 14, 2, 4, 1, 4, 2, 4, 1, 775, 1, 4, 1, 5, 1, 6, 1, 51, 13, 4, 1, 18, 1, 2, 1, 1396, 1, 34, 1, 5, 2, 2, 1, 54, 1, 2, 5, 11, 1, 12, 1, 51, 4, 2, 1, 55, 1, 4, 2, 12, 1, 6, 2, 11, 2, 2, 1, 1213, 1, 2, 2, 12, 1, 261, 1, 14, 2, 10, 1, 12, 1, 4, 4, 42, 2, 4, 1, 56, 1, 2, 1, 202, 2, 6, 6, 4, 1, 8, 1, 10494213, 15, 2, 1, 15, 1, 4, 1, 49, 1, 10, 1, 4, 6, 2, 1, 170, 2, 4, 2, 9, 1, 4, 1, 12, 1, 2, 2, 119, 1, 2, 2, 246, 1, 24, 1, 5, 4, 16, 1, 39, 1, 2, 2, 4, 1, 16, 1, 180, 1, 2, 1, 10, 1, 2, 49, 12, 1, 12, 1, 11, 1, 4, 2, 8681, 1, 5, 2, 15, 1, 6, 1, 15, 4, 2, 1, 66, 1, 4, 1, 51, 1, 30, 1, 5, 2, 4, 1, 205, 1, 6, 4, 4, 7, 4, 1, 195, 3, 6, 1, 36, 1, 2, 2, 35, 1, 6, 1, 15, 5, 2, 1, 260, 15, 2, 2, 5, 1, 32, 1, 12, 2, 2, 1, 12, 2, 4, 2, 21541, 1, 4, 1, 9, 2, 4, 1, 757, 1, 10, 5, 4, 1, 6, 2, 53, 5, 4, 1, 40, 1, 2, 2, 12, 1, 18, 1, 4, 2, 4, 1, 1280, 1, 2, 17, 16, 1, 4, 1, 53, 1, 4, 1, 51, 1, 15, 2, 42, 2, 8, 1, 5, 4, 2, 1, 44, 1, 2, 1, 36, 1, 62, 1, 1387, 1, 2, 1, 10, 1, 6, 4, 15, 1, 12, 2, 4, 1, 2, 1, 840, 1, 5, 2, 5, 2, 13, 1, 40, 504, 4, 1, 18, 1, 2, 6, 195, 2, 10, 1, 15, 5, 4, 1, 54, 1, 2, 2, 11, 1, 39, 1, 42, 1, 4, 2, 189, 1, 2, 2, 39, 1, 6, 1, 4, 2, 2, 1, 1090235, 1, 12, 1, 5, 1, 16, 4, 15, 5, 2, 1, 53, 1, 4, 5, 172, 1, 4, 1, 5, 1, 4, 2, 137, 1, 2, 1, 4, 1, 24, 1, 1211, 2, 2, 1, 15, 1, 4, 1, 14, 1, 113, 1, 16, 2, 4, 1, 205, 1, 2, 11, 20, 1, 4, 1, 12, 5, 4, 1, 30, 1, 4, 2, 1630, 2, 6, 1, 9, 13, 2, 1, 186, 2, 2, 1, 4, 2, 10, 2, 51, 2, 10, 1, 10, 1, 4, 5, 12, 1, 12, 1, 11, 2, 2, 1, 4725, 1, 2, 3, 9, 1, 8, 1, 14, 4, 4, 5, 18, 1, 2, 1, 221, 1, 68, 1, 15, 1, 2, 1, 61, 2, 4, 15, 4, 1, 4, 1, 19349, 2, 2, 1, 150, 1, 4, 7, 15, 2, 6, 1, 4, 2, 8, 1, 222, 1, 2, 4, 5, 1, 30, 1, 39, 2, 2, 1, 34, 2, 2, 4, 235, 1, 18, 2, 5, 1, 2, 2, 222, 1, 4, 2, 11, 1, 6, 1, 42, 13, 4, 1, 15, 1, 10, 1, 42, 1, 10, 2, 4, 1, 2, 1, 11394, 2, 4, 2, 5, 1, 12, 1, 42, 2, 4, 1, 900, 1, 2, 6, 51, 1, 6, 2, 34, 5, 2, 1, 46, 1, 4, 2, 11, 1, 30, 1, 196, 2, 6, 1, 10, 1, 2, 15, 199, 1, 4, 1, 4, 2, 2, 1, 954, 1, 6, 2, 13, 1, 23, 2, 12, 2, 2, 1, 37, 1, 4, 2, 49487367289, 4, 66, 2, 5, 19, 4, 1, 54, 1, 4, 2, 11, 1, 4, 1, 231, 1, 2, 1, 36, 2, 2, 2, 12, 1, 40, 1, 4, 51, 4, 2, 1028, 1, 5, 1, 15, 1, 10, 1, 35, 2, 4, 1, 12, 1, 4, 4, 42, 1, 4, 2, 5, 1, 10, 1, 583, 2, 2, 6, 4, 2, 6, 1, 1681, 6, 4, 1, 77, 1, 2, 2, 15, 1, 16, 1, 51, 2, 4, 1, 170, 1, 4, 5, 5, 1, 12, 1, 12, 2, 2, 1, 46, 1, 4, 2, 1092, 1, 8, 1, 5, 14, 2, 2, 39, 1, 4, 2, 4, 1, 254, 1, 42, 2, 2, 1, 41, 1, 2, 5, 39, 1, 4, 1, 11, 1, 10, 1, 157877, 1, 2, 4, 16, 1, 6, 1, 49, 13, 4, 1, 18, 1, 4, 1, 53, 1, 32, 1, 5, 1, 2, 2, 279, 1, 4, 2, 11, 1, 4, 3, 235, 2, 2, 1, 99, 1, 8, 2, 14, 1, 6, 1, 11, 14, 2, 1, 1040, 1, 2, 1, 13, 2, 16, 1, 12, 5, 27, 1, 12, 1, 2, 69, 1387, 1, 16, 1, 20, 2, 4, 1, 164, 4, 2, 2, 4, 1, 12, 1, 153, 2, 2, 1, 15, 1, 2, 2, 51, 1, 30, 1, 4, 1, 4, 1, 1460, 1, 55, 4, 5, 1, 12, 2, 14, 1, 4, 1, 131, 1, 2, 2, 42, 3, 6, 1, 5, 5, 4, 1, 44, 1, 10, 3, 11, 1, 10, 1, 1116461, 5, 2, 1, 10, 1, 2, 4, 35, 1, 12, 1, 11, 1, 2, 1, 3609, 1, 4, 2, 50, 1, 24, 1, 12, 2, 2, 1, 18, 1, 6, 2, 244, 1, 18, 1, 9, 2, 2, 1, 181, 1, 2, 51, 4, 2, 12, 1, 42, 1, 8, 5, 61, 1, 4, 1, 12, 1, 6, 1, 11, 2, 4, 1, 11720, 1, 2, 1, 5, 1, 112, 1, 52, 1, 2, 2, 12, 1, 4, 4, 245, 1, 4, 1, 9, 5, 2, 1, 211, 2, 4, 2, 38, 1, 6, 15, 195, 15, 6, 2, 29, 1, 2, 1, 14, 1, 32, 1, 4, 2, 4, 1, 198, 1, 4, 8, 5, 1, 4, 1, 153, 1, 2, 1, 227, 2, 4, 5, 19324, 1, 8, 1, 5, 4, 4, 1, 39, 1, 2, 2, 15, 4, 16, 1, 53, 6, 4, 1, 40, 1, 12, 5, 12, 1, 4, 2, 4, 1, 2, 1, 5958, 1, 4, 5, 12, 2, 6, 1, 14, 4, 10, 1, 40, 1, 2, 2, 179, 1, 1798, 1, 15, 2, 4, 1, 61, 1, 2, 5, 4, 1, 46, 1, 1387, 1, 6, 2, 36, 2, 2, 1, 49, 1, 24, 1, 11, 10, 2, 1, 222, 1, 4, 3, 5, 1, 10, 1, 41, 2, 4, 1, 174, 1, 2, 2, 195, 2, 4, 1, 15, 1, 6, 1, 889, 1, 2, 2, 4, 1, 12, 2, 178, 13, 2, 1, 15, 4, 4, 1, 12, 1, 20, 1, 4, 5, 4, 1, 408641062, 1, 2, 60, 36, 1, 4, 1, 15, 2, 2, 1, 46, 1, 16, 1, 54, 1, 24, 2, 5, 2, 4, 1, 221, 1, 4, 1, 11, 1, 30, 1, 928, 2, 4, 1, 10, 2, 2, 13, 14, 1, 4, 1, 11, 2, 6, 1, 697, 1, 4, 3, 5, 1, 8, 1, 12, 5, 2, 2, 64, 1, 4, 2, 10281, 1, 10, 1, 5, 1, 4, 1, 54, 1, 8, 2, 11, 1, 4, 1, 51, 6, 2, 1, 477, 1, 2, 2, 56, 5, 6, 1, 11, 5, 4, 1, 1213, 1, 4, 2, 5, 1, 72, 1, 68, 2, 2, 1, 12, 1, 2, 13, 42, 1, 38, 1, 9, 2, 2, 2, 137, 1, 2, 5, 11, 1, 6, 1, 21507, 5, 10, 1, 15, 1, 4, 1, 34, 2, 60, 2, 4, 5, 2, 1, 1005, 2, 5, 2, 5, 1, 4, 1, 12, 1, 10, 1, 30, 1, 10, 1, 235, 1, 6, 1, 50, 309, 4, 2, 39, 7, 2, 1, 11, 1, 36, 2, 42, 2, 2, 5, 40, 1, 2, 2, 39, 1, 12, 1, 4, 3, 2, 1, 47937, 1, 4, 2, 5, 1, 13, 1, 35, 4, 4, 1, 37, 1, 4, 2, 51, 1, 16, 1, 9, 1, 30, 2, 64, 1, 2, 14, 4, 1, 4, 1, 1285, 1, 2, 1, 228, 1, 2, 5, 53, 1, 8, 2, 4, 2, 2, 4, 260, 1, 6, 1, 15, 1, 110, 1, 12, 2, 4, 1, 12, 1, 4, 5, 1083553, 1, 12, 1, 5, 1, 4, 1, 749, 1, 4, 2, 11, 3, 30, 1, 54, 13, 6, 1, 15, 2, 2, 9, 12, 1, 10, 1, 35, 2, 2, 1, 1264, 2, 4, 6, 5, 1, 18, 1, 14, 2, 4, 1, 117, 1, 2, 2, 178, 1, 6, 1, 5, 4, 4, 1, 162, 2, 10, 1, 4, 1, 16, 1, 1630, 2, 2, 2, 56, 1, 10, 15, 15, 1, 4, 1, 4, 2, 12, 1, 1096, 1, 2, 21, 9, 1, 6, 1, 39, 5, 2, 1, 18, 1, 4, 2, 195, 1, 120, 1, 9, 2, 2, 1, 54, 1, 4, 4, 36, 1, 4, 1, 186, 2, 2, 1, 36, 1, 6, 15, 12, 1, 8, 1, 4, 5, 4, 1, 241004, 1, 5, 1, 15, 4, 10, 1, 15, 2, 4, 1, 34, 1, 2, 4, 167, 1, 12, 1, 15, 1, 2, 1, 3973, 1, 4, 1, 4, 1, 40, 1, 235, 11, 2, 1, 15, 1, 6, 1, 144, 1, 18, 1, 4, 2, 2, 2, 203, 1, 4, 15, 15, 1, 12, 2, 39, 1, 4, 1, 120, 1, 2, 2, 1388, 1, 6, 1, 13, 4, 4, 1, 39, 1, 2, 5, 4, 1, 66, 1, 963, 1, 8, 1, 10, 2, 4, 4, 12, 2, 12, 1, 4, 2, 4, 2, 6538, 1, 2, 2, 20, 1, 6, 2, 46, 63, 2, 1, 88, 1, 12, 1, 42, 1, 10, 2, 5, 5, 2, 1, 175, 2, 2, 2, 11, 1, 12, 1, undefined]
a000031 = Sequence $ 1 : ofPositive (\n -> (`div` n) $ sum $ map (\d -> AF.totient n * 2 ^ (n `div` d)) $ AF.divisorsList n)
a000058 = Sequence $ iterate (\n -> n * n - n + 1) 2
a008279 = Sequence $ concatMap (zipWith (*) $ IL.toList Rec.factorial) (IL.toList Rec.binomial)
a001057 = Sequence $ 0 : concatMap (\x -> [x, -x]) (enumFrom 1)
a000161 = Sequence $ ofIndices $ \n -> genericLength $ filter isSquare [n - k * k | k <- [0..intSquareRoot n]]
a001489 = Sequence $ ofIndices negate
a001478 = Sequence $ ofPositive negate
a022958 = Sequence $ ofIndices $ \n -> 2 - n
a022996 = Sequence $ ofIndices $ \n -> 40 - n
a109613 = Sequence $ ofIndices $ \n -> 2 * (n `div` 2) + 1
a008585 = Sequence $ ofIndices $ \n -> 3 * n
a069074 = Sequence $ ofIndices $ \n -> (2 * n + 2) * (2 * n + 3) * (2 * n + 4)
a010709 = Sequence $ repeat 4
a059841 = Sequence $ cycle [1, 0]
a000034 = Sequence $ cycle [1, 2]
a033999 = Sequence $ cycle [1, -1]
a010684 = Sequence $ cycle [1, 3]
a010685 = Sequence $ cycle [1, 4]
a010673 = Sequence $ cycle [0, 2]
a010674 = Sequence $ cycle [0, 3]
a010688 = Sequence $ cycle [1, 7]
a105397 = Sequence $ cycle [4, 2]
a049347 = Sequence $ cycle [1, -1, 0]
a011655 = Sequence $ cycle [0, 1, 1]
a061347 = Sequence $ cycle [1, 1, -2]
a102283 = Sequence $ cycle [0, 1, -1]
a130196 = Sequence $ cycle [1, 2, 2]
a131534 = Sequence $ cycle [1, 2, 1]
a010882 = Sequence $ cycle [1, 2, 3]
a153727 = Sequence $ cycle [1, 4, 2]
a080425 = Sequence $ cycle [0, 2, 1]
a144437 = Sequence $ cycle [3, 3, 1]
a131713 = Sequence $ cycle [1, -2, 1]
a130784 = Sequence $ cycle [1, 3, 2]
a169609 = Sequence $ cycle [1, 3, 3]
a131561 = Sequence $ cycle [1, 1, -1]
a052901 = Sequence $ cycle [3, 2, 2]
a274339 = Sequence $ cycle [15, 24, 18]
a073636 = Sequence $ cycle [1, 8, 9]
a101000 = Sequence $ cycle [0, 1, 3]
a131598 = Sequence $ cycle [2, 5, 8]
a177702 = Sequence $ cycle [1, 1, 2]
a131756 = Sequence $ cycle [2, -1, 3]
a132677 = Sequence $ cycle [1, 2, -3]
a146325 = Sequence $ cycle [1, 4, 1]
a173259 = Sequence $ cycle [4, 1, 4]
a164360 = Sequence $ cycle [5, 4, 3]
a079978 = Sequence $ cycle [1, 0, 0]
a000009 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 2
a000726 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 3
a001935 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 4
a035959 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 5
a219601 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 6
a035985 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 7
a261775 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 8
a104502 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 9
a261776 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 10
a328545 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 11
a328546 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 12
a001970 = Sequence $ eulerTransform $ drop 1 $ IL.toList Rec.partition
a034691 = Sequence $ eulerTransform $ scanl (*) 1 $ repeat 2
a034899 = Sequence $ eulerTransform $ scanl (*) 2 $ repeat 2
a166861 = Sequence $ eulerTransform fibonacci' where fibonacci' = 1 : 1 : zipWith (+) fibonacci' (drop 1 fibonacci')
a000335 = Sequence $ eulerTransform' $ ofPositive $ \n -> n * (n + 1) * (n + 2) `div` 6
a005928 = Sequence $ eulerTransform $ cycle [-3, -3, -2]
a073592 = Sequence $ eulerTransform $ ofPositive negate
a061256 = Sequence $ eulerTransform $ ofPositive $ AF.sigma 1
a061255 = Sequence $ eulerTransform $ ofPositive AF.totient
a000332 = Sequence $ ofIndices $ \n -> binomial n 4
a000391 = Sequence $ eulerTransform' $ drop 4 $ ofIndices $ \n -> binomial n 4
a005043 = Sequence riordan where riordan = 1 : 0 : zipWith (\(nm, np) (a1, a2) -> (nm * (3 * a1 + 2 * a2)) `div` np) (zip [1..] [3..]) (zip riordan (drop 1 riordan))
-- a358451 = Sequence $ inverseEulerTransform riordan where riordan = 1 : 0 : zipWith (\(nm, np) (a1, a2) -> (nm * (3 * a1 + 2 * a2)) `div` np) (zip [1..] [3..]) (zip riordan (drop 1 riordan))
a061257 = Sequence $ eulerTransform $ ofPositive AF.carmichael
a000389 = Sequence $ ofIndices $ \n -> binomial n 5
a000417 = Sequence $ eulerTransform' $ drop 5 $ ofIndices $ \n -> binomial n 5
a000579 = Sequence $ ofIndices $ \n -> binomial n 6
a000428 = Sequence $ eulerTransform' $ drop 6 $ ofIndices $ \n -> binomial n 6
a107895 = Sequence $ eulerTransform $ drop 1 $ IL.toList Rec.factorial
a030009 = Sequence $ eulerTransform $ map unPrime primes
a092119 = Sequence $ eulerTransform $ ofPositive $ \n -> adicValuation 2 $ n * 2
a051064 = Sequence $ ofPositive $ \n -> adicValuation 3 $ n * 3
a173241 = Sequence $ eulerTransform $ ofPositive $ \n -> adicValuation 3 $ n * 3
a261031 = Sequence $ eulerTransform lucas' where lucas' = 1 : 3 : zipWith (+) lucas' (drop 1 lucas')
a030012 = Sequence $ eulerTransform' $ 1 : map unPrime primes
