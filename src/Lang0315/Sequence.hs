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
) where

import Control.Monad ((>=>))
import Data.Bifunctor (bimap)
import Data.List (genericIndex, genericReplicate, genericLength, sort, sortOn)
import Data.Ord (Down(..))
import Data.Maybe (isNothing, isJust, catMaybes)
import Data.Ratio
import Data.Universe.Helpers (diagonals)

import Data.Bits (popCount)
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

ofIndices :: (Integer -> a) -> [a]
ofIndices f = map f $ enumFrom 0

ofPositive :: (Integer -> a) -> [a]
ofPositive f = map f $ enumFrom 1

binomial :: Integer -> Integer -> Integer
binomial n k = Rec.binomialLine n `genericIndex` k

stirling2 :: Integer -> Integer -> Integer
stirling2 n k = Rec.stirling2 `infiniteIndex` n `genericIndex` k

infiniteIndex :: IL.Infinite a -> Integer -> a
infiniteIndex xs i | i < 0 = error "Negative index!"
                   | otherwise = IL.foldr (\x acc m -> if m == 0 then x else acc (m - 1)) xs i

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
a000002, a003056, a000593, a001097, a006882 :: Sequence
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
a000041 = Sequence $ ofIndices $ infiniteIndex Rec.partition
a000290 = Sequence $ ofIndices $ \n -> n * n
a001222 = Sequence $ ofPositive $ fromIntegral . AF.bigOmega
a000142 = Sequence $ ofIndices $ infiniteIndex Rec.factorial
a001221 = Sequence $ ofPositive AF.smallOmega
a000720 = Sequence $ ofPositive primeCount
a007318 = Sequence $ ofIndices $ genericIndex $ concat $ IL.toList Rec.binomial
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
a008277 = Sequence $ ofIndices $ genericIndex $ concatMap (drop 1) (IL.toList Rec.stirling2)
a000312 = Sequence $ ofIndices $ \n -> n ^ n
a000302 = Sequence $ ofIndices $ \n -> 4 ^ n
a000670 = Sequence $ ofIndices $ \n -> sum $ map (\k -> stirling2 n k * Rec.factorial `infiniteIndex` k) [0..n]
a001006 = Sequence $ ofIndices $ \n -> sum $ map (\k -> (binomial (2 * k) k `div` (k + 1)) * binomial n (2 * k)) [0..n `div` 2]
a010060 = Sequence $ ofIndices $ (`mod` 2) . fromIntegral . popCount
a001065 = Sequence $ ofPositive $ \n -> AF.sigma 1 n - n
a055642 = Sequence $ ofIndices $ let go count m = if m >= 10 then go (count + 1) (m `div` 10) else count in go 1
a000079 = Sequence $ ofIndices $ \n -> 2 ^ n
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
a008292 = Sequence $ ofIndices $ genericIndex $ concat $ IL.toList Rec.eulerian1
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
