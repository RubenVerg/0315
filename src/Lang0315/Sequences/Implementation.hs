{-# LANGUAGE PatternSynonyms, ViewPatterns #-}

module Lang0315.Sequences.Implementation where

import Lang0315.Sequence
import Lang0315.Util
import Lang0315.PowerSeries (PowerSeries(..))
import qualified Lang0315.PowerSeries as PS

import Control.Monad ((>=>))
import Data.List (genericIndex, genericReplicate, genericLength, sort, sortOn, group, inits, tails)
import Data.Ord (Down(..))
import Data.Ratio
import Data.Maybe (isNothing, isJust, fromMaybe)

import Data.Bits (popCount)
import Data.Bits.Bitwise (toListLE)
import Math.NumberTheory.Primes (nextPrime, primes, unPrime, factorise, isPrime, UniqueFactorisation, Prime)
import Math.NumberTheory.Primes.Counting (primeCount, nthPrime)
import qualified Math.NumberTheory.ArithmeticFunctions as AF
import qualified Math.NumberTheory.Recurrences as Rec
import Data.Number.CReal (CReal, showCReal)

import qualified Data.List.Infinite as IL

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

generalizedPsiA :: Integral n => Word -> AF.ArithmeticFunction n n
generalizedPsiA k = AF.multiplicative (\p e -> unPrime p ^ (k * e) + unPrime p ^ (k * (e - 1)))

generalizedPsi :: (UniqueFactorisation n, Integral n) => Word -> n -> n
generalizedPsi = AF.runFunction . generalizedPsiA

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

eulerTransform'G :: Fractional a => [a] -> [a]
eulerTransform'G as = bs where
  cs = map (sum . map (\d -> fromInteger d * as `genericIndex` (d - 1)) . AF.divisorsList) [1..]
  bs = zipWith f (map fromInteger [1..]) $ map reverse $ drop 1 $ inits cs
  f n (cn : ci) = (cn + sum (zipWith (*) bs ci)) / n
  f _ _ = error "Unreachable"

eulerTransformG :: Fractional a => [a] -> [a]
eulerTransformG = (1:) . eulerTransform'G

eulerTransform' :: Integral a => [a] -> [a]
eulerTransform' = map unDivisiblePromise . eulerTransform'G . map DivisiblePromise

eulerTransform :: Integral a => [a] -> [a]
eulerTransform = map unDivisiblePromise . eulerTransformG . map DivisiblePromise

inverseEulerTransform :: [Integer] -> [Integer]
inverseEulerTransform bs = as where
  cs = zipWith f [1..] $ map reverse $ drop 1 $ inits bs
  f n (bn : bi) = n * bn - sum (zipWith (*) cs bi)
  f _ _ = error "Unreachable"
  as = map (\n -> flip div n $ sum $ map (\d -> cs `genericIndex` (d - 1) * AF.runMoebius (AF.moebius $ n `div` d)) $ AF.divisorsList n) [1..]

binomialTransform :: [Integer] -> [Integer]
binomialTransform as = zipWith (sum .: zipWith (*)) (IL.toList Rec.binomial) (drop 1 $ inits as)

inverseBinomialTransform :: [Integer] -> [Integer]
inverseBinomialTransform as = zipWith3 (\n -> sum .: zipWith3 (\k bn a -> (-1) ^ (n - k) * bn * a) [0..]) [0::Integer ..] (IL.toList Rec.binomial) (drop 1 $ inits as)

nTimes :: Int -> (a -> a) -> a -> a
nTimes 0 _ = id
nTimes 1 f = f
nTimes n f = f . nTimes (n - 1) f

nBonacci :: Int -> [Integer]
nBonacci n = sq where sq = replicate (n - 1) 0 ++ 1 : foldl' (zipWith (+)) (repeat 0) (take n $ tails sq)

pattern X :: Num a => PowerSeries a
pattern X <- (const Nothing -> Just ())
  where X = PS.fromCoefficients [0, 1]

egf' :: Num a => PowerSeries a -> [a]
egf' x = IL.toList $ IL.zipWith (*) (IL.map fromInteger Rec.factorial) (coefficients' x)

egf :: Integral a => PowerSeries (Ratio a) -> [a]
egf = map numerator . egf'

badSinCosRatio :: (Eq a, Integral a) => Ratio a -> (Ratio a, Ratio a)
badSinCosRatio 0 = (0, 1)
badSinCosRatio _ = error "sin or cos on a nonzero rational"

sinCosR :: (Eq a, Integral a) => PowerSeries (Ratio a) -> (PowerSeries (Ratio a), PowerSeries (Ratio a))
sinCosR = PS.sinCos' badSinCosRatio

sinhCoshR :: (Eq a, Integral a) => PowerSeries (Ratio a) -> (PowerSeries (Ratio a), PowerSeries (Ratio a))
sinhCoshR = PS.sinhCosh' badSinCosRatio

badExpRatio :: (Eq a, Integral a) => Ratio a -> Ratio a
badExpRatio 0 = 1
badExpRatio _ = error "exp on a nonzero rational"

expR :: (Eq a, Integral a) => PowerSeries (Ratio a) -> PowerSeries (Ratio a)
expR = PS.exp' badExpRatio

badLogRatio :: (Eq a, Integral a) => Ratio a -> Ratio a
badLogRatio 1 = 0
badLogRatio _ = error "log on a non-1 rational"

logR :: (Eq a, Integral a) => PowerSeries (Ratio a) -> PowerSeries (Ratio a)
logR = PS.log' badLogRatio

bellNumbers :: [Integer]
bellNumbers = flip map [0..] $ sum . infiniteIndex Rec.stirling2

makeArithmeticDerivative :: (UniqueFactorisation n, Integral n) => (Prime n -> n) -> (n -> n)
makeArithmeticDerivative f = go where
  go 0 = 0
  go 1 = 0
  go n = numerator $ (n % 1) * sum (map (\(p, e) -> fromIntegral e * f p % unPrime p) $ factorise n)

-- See LICENSE.OEIS
-- https://oeis.org/

-- |A000012: Always one
a000012 :: Sequence
a000012 = Sequence $ repeat 1
-- |A001477: Nonnegative integers
a001477 :: Sequence
a001477 = Sequence $ enumFrom 0
-- |A000027: Positive integers
a000027 :: Sequence
a000027 = Sequence $ enumFrom 1
-- |A000040: Prime numbers
a000040 :: Sequence
a000040 = Sequence $ map unPrime primes
-- |A000203: Sum of the divisors of n
a000203 :: Sequence
a000203 = Sequence $ ofPositive $ AF.sigma 1
-- |A000005: Number of divisors of n
a000005 :: Sequence
a000005 = Sequence $ ofPositive AF.tau
-- |A000217: Triangular numbers
a000217 :: Sequence
a000217 = Sequence $ ofIndices $ \n -> n * (n + 1) `div` 2
-- |A000010: Euler totient function
a000010 :: Sequence
a000010 = Sequence $ ofPositive AF.totient
-- |A000108: Catalan numbers
a000108 :: Sequence
a000108 = Sequence $ ofIndices $ \n -> binomial (2 * n) n `div` (n + 1)
-- |A000041: Number of partitions of n
a000041 :: Sequence
a000041 = Sequence $ IL.toList Rec.partition
-- |A000290: Square numbers
a000290 :: Sequence
a000290 = Sequence $ ofIndices $ \n -> n * n
-- |A001222: Number of prime divisors of n counted with multiplicity
a001222 :: Sequence
a001222 = Sequence $ ofPositive $ fromIntegral . AF.bigOmega
-- |A000142: Factorial numbers
a000142 :: Sequence
a000142 = Sequence $ ofIndices $ infiniteIndex Rec.factorial
-- |A001221: Number of distinct primes dividing n
a001221 :: Sequence
a001221 = Sequence $ ofPositive AF.smallOmega
-- |A000720: Number of primes <= n
a000720 :: Sequence
a000720 = Sequence $ ofPositive primeCount
-- |A007318: Pascal's triangle read by rows
a007318 :: Sequence
a007318 = Sequence $ concat $ IL.toList Rec.binomial
-- |A000120: Number of ones in binary expansion of n
a000120 :: Sequence
a000120 = Sequence $ ofIndices $ fromIntegral . popCount
-- |A005117: Squarefree numbers
a005117 :: Sequence
a005117 = Sequence $ ofIndices $ genericIndex $ AF.nFrees 2
-- |A002110: Primorial numbers
a002110 :: Sequence
a002110 = Sequence $ ofIndices $ \case
  0 -> 1
  n -> product $ map unPrime [nextPrime 1..nthPrime (fromEnum n)]
-- |A001622: Decimal expansion of golden ratio 
a001622 :: Sequence
a001622 = Sequence $ digitSequence realPhi
-- |A001358: Semiprimes
a001358 :: Sequence
a001358 = Sequence $ filter (\n -> AF.bigOmega n == 2) $ enumFrom 1
-- |A008683: Möbius function
a008683 :: Sequence
a008683 = Sequence $ ofPositive $ AF.runMoebius . AF.moebius
-- |A000032: Lucas numbers beginning at 2
a000032 :: Sequence
a000032 = Sequence lucas where lucas = 2 : 1 : zipWith (+) lucas (drop 1 lucas)
-- |A000225: 2^n - 1
a000225 :: Sequence
a000225 = Sequence $ map (subtract 1) $ iterate (* 2) 1
-- |A000110: Bell or exponential numbers
a000110 :: Sequence
a000110 = Sequence bellNumbers
-- |A005408: The odd numbers
a005408 :: Sequence
a005408 = Sequence $ ofIndices $ \n -> 2 * n + 1
-- |A002275: Repunits: (10^n - 1)/9
a002275 :: Sequence
a002275 = Sequence $ ofIndices $ \n -> (10 ^ n - 1) `div` 9
-- |A006530: Greatest prime dividing n
a006530 :: Sequence
a006530 = Sequence $ ofPositive $ \n -> case sortOn Down $ factorise n of
  [] -> 1
  ((p, _):_) -> unPrime p
-- |A000007: A one and then always zero
a000007 :: Sequence
a000007 = Sequence $ 1 : repeat 0
-- |A000796: Decimal expansion of pi
a000796 :: Sequence
a000796 = Sequence $ digitSequence pi
-- |A000961: Powers of primes
a000961 :: Sequence
a000961 = Sequence $ filter (\n -> AF.smallOmega n <= (1 :: Integer)) $ enumFrom 1
-- |A000984: Central binomial coefficients
a000984 :: Sequence
a000984 = Sequence $ ofIndices $ \n -> binomial (2 * n) n
-- |A000578: Cube numbers
a000578 :: Sequence
a000578 = Sequence $ ofIndices $ \n -> n * n * n
-- |A002808: The composite numbers
a002808 :: Sequence
a002808 = Sequence $ filter (isNothing . isPrime) $ enumFrom 2 -- 1 is not part of the sequence
-- |A020639: Least prime dividing n
a020639 :: Sequence
a020639 = Sequence $ ofPositive $ \n -> case sort $ factorise n of
  [] -> 1
  ((p, _):_) -> unPrime p
-- |A000244: Powers of three
a000244 :: Sequence
a000244 = Sequence $ iterate (* 3) 1
-- |A070939: Length of binary representation of n
a070939 :: Sequence
a070939 = Sequence $ 1 : 1 : chunk [1] where chunk xs = let rs = map (+ 1) (xs ++ xs) in rs ++ chunk rs
-- |A000292: Tetrahedral numbers
a000292 :: Sequence
a000292 = Sequence $ ofIndices $ \n -> n * (n + 1) * (n + 2) `div` 6
-- |A002113: Palindromes in base 10
a002113 :: Sequence
a002113 = Sequence $ filter ((==) <*> reverseDigits) $ enumFrom 0
-- |A000129: Pell numbers
a000129 :: Sequence
a000129 = Sequence pell where pell = 0 : 1 : zipWith (+) pell (map (2 *) $ drop 1 pell)
-- |A005843: The nonnegative even numbers
a005843 :: Sequence
a005843 = Sequence $ ofIndices $ \n -> 2 * n
-- |A000035: Parity of n
a000035 :: Sequence
a000035 = Sequence $ cycle [0, 1]
-- |A001045: Jacobsthal sequence
a001045 :: Sequence
a001045 = Sequence jacobsthal where jacobsthal = 0 : 1 : zipWith (+) (map (2 *) jacobsthal) (drop 1 jacobsthal)
-- |A001113: Decimal expansion of e
a001113 :: Sequence
a001113 = Sequence $ digitSequence $ exp 1
-- |A000396: Perfect numbers k
a000396 :: Sequence
a000396 = Sequence $ known ++ filter (\n -> AF.sigma 1 n == 2 * n) (enumFrom $ 1 + maximum known) where
  known = [6, 28, 496, 8128, 33550336, 8589869056, 137438691328, 2305843008139952128, 2658455991569831744654692615953842176, 191561942608236107294793378084303638130997321548169216, 13164036458569648337239753460458722910223472318386943117783728128]
-- |A000043: Mersenne exponents
a000043 :: Sequence
a000043 = Sequence $ known ++ filter (\n -> isJust $ isPrime $ (2 :: Integer) ^ n - 1) (enumFrom $ 1 + maximum known) where
  known = [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127, 521, 607, 1279, 2203, 2281, 3217, 4253, 4423, 9689, 9941, 11213, 19937, 21701, 23209, 44497, 86243, 110503, 132049, 216091, 756839, 859433, 1257787, 1398269, 2976221, 3021377, 6972593, 13466917, 20996011, 24036583, 25964951, 30402457, 32582657, 37156667, 42643801, 43112609, 57885161, 74207281, 77232917]
-- |A001764: binomial(3*n,n)/(2*n+1)
a001764 :: Sequence
a001764 = Sequence $ ofIndices $ \n -> binomial (3 * n) n `div` (2 * n + 1)
-- |A001147: Double factorial of odd numbers
a001147 :: Sequence
a001147 = Sequence $ scanl (\acc n -> acc * (2 * n + 1)) 1 $ enumFrom 0
-- |A008277: Triangle of Stirling numbers of the second kind
a008277 :: Sequence
a008277 = Sequence $ concatMap (drop 1) (IL.toList Rec.stirling2)
-- |A000312: n^n
a000312 :: Sequence
a000312 = Sequence $ ofIndices $ \n -> n ^ n
-- |A000302: Powers of four
a000302 :: Sequence
a000302 = Sequence $ scanl (*) 1 $ repeat 4
-- |A000670: Fubini numbers
a000670 :: Sequence
a000670 = Sequence $ ofIndices $ \n -> sum $ map (\k -> stirling2 n k * Rec.factorial `infiniteIndex` k) [0..n]
-- |A001006: Motzkin numbers
a001006 :: Sequence
a001006 = Sequence $ ofIndices $ \n -> sum $ map (\k -> (binomial (2 * k) k `div` (k + 1)) * binomial n (2 * k)) [0..n `div` 2]
-- |A010060: Thue-Morse sequence
a010060 :: Sequence
a010060 = Sequence $ ofIndices $ (`mod` 2) . fromIntegral . popCount
-- |A001065: Sum of proper divisors of n
a001065 :: Sequence
a001065 = Sequence $ ofPositive $ \n -> AF.sigma 1 n - n
-- |A055642: Number of digits in the decimal expansion of n
a055642 :: Sequence
a055642 = Sequence $ ofIndices $ let go count m = if m >= 10 then go (count + 1) (m `div` 10) else count in go 1
-- |A000079: Powers of two
a000079 :: Sequence
a000079 = Sequence $ scanl (*) 1 $ repeat 2
-- |A100995: If n is a prime power p^m, m >= 1, then m, otherwise 0
a100995 :: Sequence
a100995 = Sequence $ ofPositive $ \n -> case factorise n of
  [(_, e)] -> fromIntegral e
  _ -> 0
-- |A014963: Exponential of Mangoldt function M(n)
a014963 :: Sequence
a014963 = Sequence $ ofPositive $ \n -> case factorise n of
  [(p, _)] -> unPrime p
  _ -> 1
-- |A023443: Numbers from negative one
a023443 :: Sequence
a023443 = Sequence $ enumFrom $ negate 1
-- |A000326: Pentagonal numbers
a000326 :: Sequence
a000326 = Sequence $ ofIndices $ \n -> n * (3 * n - 1) `div` 2
-- |A000166: Number of derangements
a000166 :: Sequence
a000166 = Sequence subfact where subfact = 1 : 0 : zipWith (*) [1..] (zipWith (+) subfact $ drop 1 subfact)
-- |A000330: Square pyramidal numbers
a000330 :: Sequence
a000330 = Sequence $ ofIndices $ \n -> n * (n + 1) * (2 * n + 1) `div` 6
-- |A002620: Quarter-squares
a002620 :: Sequence
a002620 = Sequence $ ofIndices $ \n -> n * n `div` 4
-- |A001511: The ruler function
a001511 :: Sequence
a001511 = Sequence $ ofPositive $ \n -> adicValuation 2 $ n * 2
-- |A004526: Nonnegative integers repeated
a004526 :: Sequence
a004526 = Sequence $ ofIndices $ \n -> n `div` 2
-- |A000085: Number of self-inverse permutations on n letters
a000085 :: Sequence
a000085 = Sequence involutions where involutions = 1 : 1 : zipWith (+) (zipWith (*) [1..] involutions) (drop 1 involutions)
-- |A001227: Number of odd divisors
a001227 :: Sequence
a001227 = Sequence $ ofPositive $ \n -> AF.tau n `div` (adicValuation 2 n + 1)
-- |A001906: Bisection of Fibonacci sequence
a001906 :: Sequence
a001906 = Sequence evenFibonacci where evenFibonacci = 0 : 1 : zipWith subtract evenFibonacci (map (* 3) $ drop 1 evenFibonacci)
-- |A000124: Central polygonal numbers
a000124 :: Sequence
a000124 = Sequence $ ofIndices $ \n -> n * (n + 1) `div` 2 + 1
-- |A001405: binomial(n, floor(n/2))
a001405 :: Sequence
a001405 = Sequence $ ofIndices $ \n -> binomial n (n `div` 2)
-- |A000583: Fourth powers
a000583 :: Sequence
a000583 = Sequence $ ofIndices $ \n -> n * n * n * n
-- |A018252: Nonprime numbers
a018252 :: Sequence
a018252 = Sequence $ filter (isNothing . isPrime) $ enumFrom 1
-- |A001157: Sum of squares of divisors of n
a001157 :: Sequence
a001157 = Sequence $ ofPositive $ AF.sigma 2
-- |A001700: binomial(2*n+1, n+1)
a001700 :: Sequence
a001700 = Sequence $ ofIndices $ \n -> binomial (2 * n + 1) (n + 1)
-- |A008292: Triangle of Eulerian numbers
a008292 :: Sequence
a008292 = Sequence $ concat $ IL.toList Rec.eulerian1
-- |A005101: Abundant numbers
a005101 :: Sequence
a005101 = Sequence $ filter (\n -> AF.sigma 1 n > 2 * n) $ enumFrom 1
-- |A001615: Dedekind psi function
a001615 :: Sequence
a001615 = Sequence $ ofPositive $ generalizedPsi 1
-- |A003418: Least Common Multiple
a003418 :: Sequence
a003418 = Sequence $ ofIndices $ \n -> foldl lcm 1 [1..n]
-- |A000169: Number of labeled rooted trees with n nodes
a000169 :: Sequence
a000169 = Sequence $ ofPositive $ \n -> n ^ (n - 1)
-- |A246655: Prime powers
a246655 :: Sequence
a246655 = Sequence $ filter (\n -> AF.smallOmega n == (1 :: Integer)) $ enumFrom 1
-- |A027641: Numerator of Bernoulli number
a027641 :: Sequence
a027641 = Sequence $ map numerator $ IL.toList Rec.bernoulli
-- |A027642: Denominator of Bernoulli number
a027642 :: Sequence
a027642 = Sequence $ map denominator $ IL.toList Rec.bernoulli
-- |A000272: Number of trees on n labeled nodes
a000272 :: Sequence
a000272 = Sequence $ 1 : 1 : map (\n -> n ^ (n - 2)) (enumFrom 2)
-- |A000004: Always zero
a000004 :: Sequence
a000004 = Sequence $ repeat 0
-- |A000204: Lucas numbers
a000204 :: Sequence
a000204 = Sequence lucas' where lucas' = 1 : 3 : zipWith (+) lucas' (drop 1 lucas')
-- |A000069: Odious numbers
a000069 :: Sequence
a000069 = Sequence $ filter (odd . popCount) $ enumFrom 0
-- |A002322: Carmichael lambda function
a002322 :: Sequence
a002322 = Sequence $ ofPositive AF.carmichael
-- |A001969: Evil numbers
a001969 :: Sequence
a001969 = Sequence $ filter (even . popCount) $ enumFrom 0
-- |A000002: Kolakoski sequence
a000002 :: Sequence
a000002 = Sequence kolakoski where kolakoski = 1 : 2 : drop 2 (concat $ zipWith genericReplicate kolakoski $ cycle [1, 2])
-- |A003056: Inverse of triangular numbers
a003056 :: Sequence
a003056 = Sequence $ byAntiDiagonals (+) (enumFrom 0) (enumFrom 0)
-- |A000593: Sum of odd divisors of n
a000593 :: Sequence
a000593 = Sequence $ ofPositive $ \n -> AF.sigma 1 n - if even n then 2 * AF.sigma 1 (n `div` 2) else 0
-- |A001097: Twin primes
a001097 :: Sequence
a001097 = Sequence $ map unPrime $ filter (\p -> let p' = unPrime p in unPrime (pred p) == p' - 2 || unPrime (succ p) == p' + 2) $ drop 1 primes
-- |A006882: Double factorials
a006882 :: Sequence
a006882 = Sequence df where df = 1 : 1 : zipWith (*) [2..] df
-- |A011557: Powers of ten
a011557 :: Sequence
a011557 = Sequence $ scanl (*) 1 $ repeat 10
-- |A000262: Number of sets of lists
a000262 :: Sequence
a000262 = Sequence sol where sol = 1 : 1 : zipWith subtract (zipWith (*) [1..] $ zipWith (*) [0..] sol) (zipWith (*) [3, 5..] $ drop 1 sol)
-- |A005811: Number of runs in binary expansion of n
a005811 :: Sequence
a005811 = Sequence $ 0 : ofPositive (genericLength . group . toListLE)
-- |A144944: Super-Catalan triangle
a144944 :: Sequence
a144944 = Sequence $ concat superCatalanT
-- |A001003: Schroeder's second problem
a001003 :: Sequence
a001003 = Sequence $ ofIndices $ \n -> superCatalan n n
-- |A000196: Integer part of square root of n
a000196 :: Sequence
a000196 = Sequence intSquareRoots
-- |A001481: Sum of 2 squares
a001481 :: Sequence
a001481 = Sequence $ filter (\n -> any isSquare [n - k * k | k <- [0..intSquareRoot n]]) $ enumFrom 0
-- |A005100: Deficient numbers
a005100 :: Sequence
a005100 = Sequence $ filter (\n -> AF.sigma 1 n < 2 * n) $ enumFrom 1
-- |A001037: Number of degree-n irreducible polynomials over GF(2)
a001037 :: Sequence
a001037 = Sequence $ 1 : ofPositive (\n -> (`div` n) $ sum $ map (\d -> AF.runMoebius (AF.moebius $ n `div` d) * 2 ^ d) $ AF.divisorsList n)
-- |A000594: Ramanujan's tau function
a000594 :: Sequence
a000594 = Sequence $ ofPositive AF.ramanujan
-- |A000688: Number of Abelian groups of order n
a000688 :: Sequence
a000688 = Sequence $ ofPositive $ AF.runFunction $ AF.multiplicative (\_ k -> Rec.partition `infiniteIndex` fromIntegral k)
-- |A000001: Number of groups of order n
a000001 :: Sequence
a000001 = Sequence [0, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5, 1, 2, 1, 14, 1, 5, 1, 5, 2, 2, 1, 15, 2, 2, 5, 4, 1, 4, 1, 51, 1, 2, 1, 14, 1, 2, 2, 14, 1, 6, 1, 4, 2, 2, 1, 52, 2, 5, 1, 5, 1, 15, 2, 13, 2, 2, 1, 13, 1, 2, 4, 267, 1, 4, 1, 5, 1, 4, 1, 50, 1, 2, 3, 4, 1, 6, 1, 52, 15, 2, 1, 15, 1, 2, 1, 12, 1, 10, 1, 4, 2, 2, 1, 231, 1, 5, 2, 16, 1, 4, 1, 14, 2, 2, 1, 45, 1, 6, 2, 43, 1, 6, 1, 5, 4, 2, 1, 47, 2, 2, 1, 4, 5, 16, 1, 2328, 2, 4, 1, 10, 1, 2, 5, 15, 1, 4, 1, 11, 1, 2, 1, 197, 1, 2, 6, 5, 1, 13, 1, 12, 2, 4, 2, 18, 1, 2, 1, 238, 1, 55, 1, 5, 2, 2, 1, 57, 2, 4, 5, 4, 1, 4, 2, 42, 1, 2, 1, 37, 1, 4, 2, 12, 1, 6, 1, 4, 13, 4, 1, 1543, 1, 2, 2, 12, 1, 10, 1, 52, 2, 2, 2, 12, 2, 2, 2, 51, 1, 12, 1, 5, 1, 2, 1, 177, 1, 2, 2, 15, 1, 6, 1, 197, 6, 2, 1, 15, 1, 4, 2, 14, 1, 16, 1, 4, 2, 4, 1, 208, 1, 5, 67, 5, 2, 4, 1, 12, 1, 15, 1, 46, 2, 2, 1, 56092, 1, 6, 1, 15, 2, 2, 1, 39, 1, 4, 1, 4, 1, 30, 1, 54, 5, 2, 4, 10, 1, 2, 4, 40, 1, 4, 1, 4, 2, 4, 1, 1045, 2, 4, 2, 5, 1, 23, 1, 14, 5, 2, 1, 49, 2, 2, 1, 42, 2, 10, 1, 9, 2, 6, 1, 61, 1, 2, 4, 4, 1, 4, 1, 1640, 1, 4, 1, 176, 2, 2, 2, 15, 1, 12, 1, 4, 5, 2, 1, 228, 1, 5, 1, 15, 1, 18, 5, 12, 1, 2, 1, 12, 1, 10, 14, 195, 1, 4, 2, 5, 2, 2, 1, 162, 2, 2, 3, 11, 1, 6, 1, 42, 2, 4, 1, 15, 1, 4, 7, 12, 1, 60, 1, 11, 2, 2, 1, 20169, 2, 2, 4, 5, 1, 12, 1, 44, 1, 2, 1, 30, 1, 2, 5, 221, 1, 6, 1, 5, 16, 6, 1, 46, 1, 6, 1, 4, 1, 10, 1, 235, 2, 4, 1, 41, 1, 2, 2, 14, 2, 4, 1, 4, 2, 4, 1, 775, 1, 4, 1, 5, 1, 6, 1, 51, 13, 4, 1, 18, 1, 2, 1, 1396, 1, 34, 1, 5, 2, 2, 1, 54, 1, 2, 5, 11, 1, 12, 1, 51, 4, 2, 1, 55, 1, 4, 2, 12, 1, 6, 2, 11, 2, 2, 1, 1213, 1, 2, 2, 12, 1, 261, 1, 14, 2, 10, 1, 12, 1, 4, 4, 42, 2, 4, 1, 56, 1, 2, 1, 202, 2, 6, 6, 4, 1, 8, 1, 10494213, 15, 2, 1, 15, 1, 4, 1, 49, 1, 10, 1, 4, 6, 2, 1, 170, 2, 4, 2, 9, 1, 4, 1, 12, 1, 2, 2, 119, 1, 2, 2, 246, 1, 24, 1, 5, 4, 16, 1, 39, 1, 2, 2, 4, 1, 16, 1, 180, 1, 2, 1, 10, 1, 2, 49, 12, 1, 12, 1, 11, 1, 4, 2, 8681, 1, 5, 2, 15, 1, 6, 1, 15, 4, 2, 1, 66, 1, 4, 1, 51, 1, 30, 1, 5, 2, 4, 1, 205, 1, 6, 4, 4, 7, 4, 1, 195, 3, 6, 1, 36, 1, 2, 2, 35, 1, 6, 1, 15, 5, 2, 1, 260, 15, 2, 2, 5, 1, 32, 1, 12, 2, 2, 1, 12, 2, 4, 2, 21541, 1, 4, 1, 9, 2, 4, 1, 757, 1, 10, 5, 4, 1, 6, 2, 53, 5, 4, 1, 40, 1, 2, 2, 12, 1, 18, 1, 4, 2, 4, 1, 1280, 1, 2, 17, 16, 1, 4, 1, 53, 1, 4, 1, 51, 1, 15, 2, 42, 2, 8, 1, 5, 4, 2, 1, 44, 1, 2, 1, 36, 1, 62, 1, 1387, 1, 2, 1, 10, 1, 6, 4, 15, 1, 12, 2, 4, 1, 2, 1, 840, 1, 5, 2, 5, 2, 13, 1, 40, 504, 4, 1, 18, 1, 2, 6, 195, 2, 10, 1, 15, 5, 4, 1, 54, 1, 2, 2, 11, 1, 39, 1, 42, 1, 4, 2, 189, 1, 2, 2, 39, 1, 6, 1, 4, 2, 2, 1, 1090235, 1, 12, 1, 5, 1, 16, 4, 15, 5, 2, 1, 53, 1, 4, 5, 172, 1, 4, 1, 5, 1, 4, 2, 137, 1, 2, 1, 4, 1, 24, 1, 1211, 2, 2, 1, 15, 1, 4, 1, 14, 1, 113, 1, 16, 2, 4, 1, 205, 1, 2, 11, 20, 1, 4, 1, 12, 5, 4, 1, 30, 1, 4, 2, 1630, 2, 6, 1, 9, 13, 2, 1, 186, 2, 2, 1, 4, 2, 10, 2, 51, 2, 10, 1, 10, 1, 4, 5, 12, 1, 12, 1, 11, 2, 2, 1, 4725, 1, 2, 3, 9, 1, 8, 1, 14, 4, 4, 5, 18, 1, 2, 1, 221, 1, 68, 1, 15, 1, 2, 1, 61, 2, 4, 15, 4, 1, 4, 1, 19349, 2, 2, 1, 150, 1, 4, 7, 15, 2, 6, 1, 4, 2, 8, 1, 222, 1, 2, 4, 5, 1, 30, 1, 39, 2, 2, 1, 34, 2, 2, 4, 235, 1, 18, 2, 5, 1, 2, 2, 222, 1, 4, 2, 11, 1, 6, 1, 42, 13, 4, 1, 15, 1, 10, 1, 42, 1, 10, 2, 4, 1, 2, 1, 11394, 2, 4, 2, 5, 1, 12, 1, 42, 2, 4, 1, 900, 1, 2, 6, 51, 1, 6, 2, 34, 5, 2, 1, 46, 1, 4, 2, 11, 1, 30, 1, 196, 2, 6, 1, 10, 1, 2, 15, 199, 1, 4, 1, 4, 2, 2, 1, 954, 1, 6, 2, 13, 1, 23, 2, 12, 2, 2, 1, 37, 1, 4, 2, 49487367289, 4, 66, 2, 5, 19, 4, 1, 54, 1, 4, 2, 11, 1, 4, 1, 231, 1, 2, 1, 36, 2, 2, 2, 12, 1, 40, 1, 4, 51, 4, 2, 1028, 1, 5, 1, 15, 1, 10, 1, 35, 2, 4, 1, 12, 1, 4, 4, 42, 1, 4, 2, 5, 1, 10, 1, 583, 2, 2, 6, 4, 2, 6, 1, 1681, 6, 4, 1, 77, 1, 2, 2, 15, 1, 16, 1, 51, 2, 4, 1, 170, 1, 4, 5, 5, 1, 12, 1, 12, 2, 2, 1, 46, 1, 4, 2, 1092, 1, 8, 1, 5, 14, 2, 2, 39, 1, 4, 2, 4, 1, 254, 1, 42, 2, 2, 1, 41, 1, 2, 5, 39, 1, 4, 1, 11, 1, 10, 1, 157877, 1, 2, 4, 16, 1, 6, 1, 49, 13, 4, 1, 18, 1, 4, 1, 53, 1, 32, 1, 5, 1, 2, 2, 279, 1, 4, 2, 11, 1, 4, 3, 235, 2, 2, 1, 99, 1, 8, 2, 14, 1, 6, 1, 11, 14, 2, 1, 1040, 1, 2, 1, 13, 2, 16, 1, 12, 5, 27, 1, 12, 1, 2, 69, 1387, 1, 16, 1, 20, 2, 4, 1, 164, 4, 2, 2, 4, 1, 12, 1, 153, 2, 2, 1, 15, 1, 2, 2, 51, 1, 30, 1, 4, 1, 4, 1, 1460, 1, 55, 4, 5, 1, 12, 2, 14, 1, 4, 1, 131, 1, 2, 2, 42, 3, 6, 1, 5, 5, 4, 1, 44, 1, 10, 3, 11, 1, 10, 1, 1116461, 5, 2, 1, 10, 1, 2, 4, 35, 1, 12, 1, 11, 1, 2, 1, 3609, 1, 4, 2, 50, 1, 24, 1, 12, 2, 2, 1, 18, 1, 6, 2, 244, 1, 18, 1, 9, 2, 2, 1, 181, 1, 2, 51, 4, 2, 12, 1, 42, 1, 8, 5, 61, 1, 4, 1, 12, 1, 6, 1, 11, 2, 4, 1, 11720, 1, 2, 1, 5, 1, 112, 1, 52, 1, 2, 2, 12, 1, 4, 4, 245, 1, 4, 1, 9, 5, 2, 1, 211, 2, 4, 2, 38, 1, 6, 15, 195, 15, 6, 2, 29, 1, 2, 1, 14, 1, 32, 1, 4, 2, 4, 1, 198, 1, 4, 8, 5, 1, 4, 1, 153, 1, 2, 1, 227, 2, 4, 5, 19324, 1, 8, 1, 5, 4, 4, 1, 39, 1, 2, 2, 15, 4, 16, 1, 53, 6, 4, 1, 40, 1, 12, 5, 12, 1, 4, 2, 4, 1, 2, 1, 5958, 1, 4, 5, 12, 2, 6, 1, 14, 4, 10, 1, 40, 1, 2, 2, 179, 1, 1798, 1, 15, 2, 4, 1, 61, 1, 2, 5, 4, 1, 46, 1, 1387, 1, 6, 2, 36, 2, 2, 1, 49, 1, 24, 1, 11, 10, 2, 1, 222, 1, 4, 3, 5, 1, 10, 1, 41, 2, 4, 1, 174, 1, 2, 2, 195, 2, 4, 1, 15, 1, 6, 1, 889, 1, 2, 2, 4, 1, 12, 2, 178, 13, 2, 1, 15, 4, 4, 1, 12, 1, 20, 1, 4, 5, 4, 1, 408641062, 1, 2, 60, 36, 1, 4, 1, 15, 2, 2, 1, 46, 1, 16, 1, 54, 1, 24, 2, 5, 2, 4, 1, 221, 1, 4, 1, 11, 1, 30, 1, 928, 2, 4, 1, 10, 2, 2, 13, 14, 1, 4, 1, 11, 2, 6, 1, 697, 1, 4, 3, 5, 1, 8, 1, 12, 5, 2, 2, 64, 1, 4, 2, 10281, 1, 10, 1, 5, 1, 4, 1, 54, 1, 8, 2, 11, 1, 4, 1, 51, 6, 2, 1, 477, 1, 2, 2, 56, 5, 6, 1, 11, 5, 4, 1, 1213, 1, 4, 2, 5, 1, 72, 1, 68, 2, 2, 1, 12, 1, 2, 13, 42, 1, 38, 1, 9, 2, 2, 2, 137, 1, 2, 5, 11, 1, 6, 1, 21507, 5, 10, 1, 15, 1, 4, 1, 34, 2, 60, 2, 4, 5, 2, 1, 1005, 2, 5, 2, 5, 1, 4, 1, 12, 1, 10, 1, 30, 1, 10, 1, 235, 1, 6, 1, 50, 309, 4, 2, 39, 7, 2, 1, 11, 1, 36, 2, 42, 2, 2, 5, 40, 1, 2, 2, 39, 1, 12, 1, 4, 3, 2, 1, 47937, 1, 4, 2, 5, 1, 13, 1, 35, 4, 4, 1, 37, 1, 4, 2, 51, 1, 16, 1, 9, 1, 30, 2, 64, 1, 2, 14, 4, 1, 4, 1, 1285, 1, 2, 1, 228, 1, 2, 5, 53, 1, 8, 2, 4, 2, 2, 4, 260, 1, 6, 1, 15, 1, 110, 1, 12, 2, 4, 1, 12, 1, 4, 5, 1083553, 1, 12, 1, 5, 1, 4, 1, 749, 1, 4, 2, 11, 3, 30, 1, 54, 13, 6, 1, 15, 2, 2, 9, 12, 1, 10, 1, 35, 2, 2, 1, 1264, 2, 4, 6, 5, 1, 18, 1, 14, 2, 4, 1, 117, 1, 2, 2, 178, 1, 6, 1, 5, 4, 4, 1, 162, 2, 10, 1, 4, 1, 16, 1, 1630, 2, 2, 2, 56, 1, 10, 15, 15, 1, 4, 1, 4, 2, 12, 1, 1096, 1, 2, 21, 9, 1, 6, 1, 39, 5, 2, 1, 18, 1, 4, 2, 195, 1, 120, 1, 9, 2, 2, 1, 54, 1, 4, 4, 36, 1, 4, 1, 186, 2, 2, 1, 36, 1, 6, 15, 12, 1, 8, 1, 4, 5, 4, 1, 241004, 1, 5, 1, 15, 4, 10, 1, 15, 2, 4, 1, 34, 1, 2, 4, 167, 1, 12, 1, 15, 1, 2, 1, 3973, 1, 4, 1, 4, 1, 40, 1, 235, 11, 2, 1, 15, 1, 6, 1, 144, 1, 18, 1, 4, 2, 2, 2, 203, 1, 4, 15, 15, 1, 12, 2, 39, 1, 4, 1, 120, 1, 2, 2, 1388, 1, 6, 1, 13, 4, 4, 1, 39, 1, 2, 5, 4, 1, 66, 1, 963, 1, 8, 1, 10, 2, 4, 4, 12, 2, 12, 1, 4, 2, 4, 2, 6538, 1, 2, 2, 20, 1, 6, 2, 46, 63, 2, 1, 88, 1, 12, 1, 42, 1, 10, 2, 5, 5, 2, 1, 175, 2, 2, 2, 11, 1, 12, 1, undefined]
-- |A000031: Number of n-bead necklaces with 2 colors when turning over is not allowed
a000031 :: Sequence
a000031 = Sequence $ 1 : ofPositive (\n -> (`div` n) $ sum $ map (\d -> AF.totient d * 2 ^ (n `div` d)) $ AF.divisorsList n)
-- |A000058: Sylvester's sequence
a000058 :: Sequence
a000058 = Sequence $ iterate (\n -> n * n - n + 1) 2
-- |A008279: Triangle T(n,k) = n!/(n-k)!, read by rows
a008279 :: Sequence
a008279 = Sequence $ concatMap (zipWith (*) $ IL.toList Rec.factorial) (IL.toList Rec.binomial)
-- |A001057: Canonical enumeration of integers
a001057 :: Sequence
a001057 = Sequence $ 0 : concatMap (\x -> [x, -x]) (enumFrom 1)
-- |A000161: Number of partitions of n into 2 squares
a000161 :: Sequence
a000161 = Sequence $ ofIndices $ \n -> genericLength $ filter isSquare [n - k * k | k <- [0..intSquareRoot (n `div` 2)]]
-- |A001489: Nonpositive integers
a001489 :: Sequence
a001489 = Sequence $ ofIndices negate
-- |A001478: Negative integers
a001478 :: Sequence
a001478 = Sequence $ ofPositive negate
-- |A022958: 2-n
a022958 :: Sequence
a022958 = Sequence $ ofIndices $ \n -> 2 - n
-- |A022996: 40-n
a022996 :: Sequence
a022996 = Sequence $ ofIndices $ \n -> 40 - n
-- |A109613: Odd numbers repeated twice
a109613 :: Sequence
a109613 = Sequence $ ofIndices $ \n -> 2 * (n `div` 2) + 1
-- |A008585: Multiples of three
a008585 :: Sequence
a008585 = Sequence $ ofIndices $ \n -> 3 * n
-- |A069074: (2*n+2)*(2*n+3)*(2*n+4)
a069074 :: Sequence
a069074 = Sequence $ ofIndices $ \n -> (2 * n + 2) * (2 * n + 3) * (2 * n + 4)
-- |A010709: Always four
a010709 :: Sequence
a010709 = Sequence $ repeat 4
-- |A059841: Is n even?
a059841 :: Sequence
a059841 = Sequence $ cycle [1, 0]
-- |A000034: Cycle the numbers 1, 2
a000034 :: Sequence
a000034 = Sequence $ cycle [1, 2]
-- |A033999: Cycle the numbers 1, -1
a033999 :: Sequence
a033999 = Sequence $ cycle [1, -1]
-- |A010684: Cycle the numbers 1, 3
a010684 :: Sequence
a010684 = Sequence $ cycle [1, 3]
-- |A010685: Cycle the numbers 1, 4
a010685 :: Sequence
a010685 = Sequence $ cycle [1, 4]
-- |A010673: Cycle the numbers 0, 2
a010673 :: Sequence
a010673 = Sequence $ cycle [0, 2]
-- |A010674: Cycle the numbers 0, 3
a010674 :: Sequence
a010674 = Sequence $ cycle [0, 3]
-- |A010688: Cycle the numbers 1, 7
a010688 :: Sequence
a010688 = Sequence $ cycle [1, 7]
-- |A105397: Cycle the numbers 4, 2
a105397 :: Sequence
a105397 = Sequence $ cycle [4, 2]
-- |A049347: Cycle the numbers 1, -1, 0
a049347 :: Sequence
a049347 = Sequence $ cycle [1, -1, 0]
-- |A011655: Cycle the numbers 0, 1, 1
a011655 :: Sequence
a011655 = Sequence $ cycle [0, 1, 1]
-- |A061347: Cycle the numbers 1, 1, -2
a061347 :: Sequence
a061347 = Sequence $ cycle [1, 1, -2]
-- |A102283: Cycle the numbers 0, 1, -1
a102283 :: Sequence
a102283 = Sequence $ cycle [0, 1, -1]
-- |A130196: Cycle the numbers 1, 2, 2
a130196 :: Sequence
a130196 = Sequence $ cycle [1, 2, 2]
-- |A131534: Cycle the numbers 1, 2, 1
a131534 :: Sequence
a131534 = Sequence $ cycle [1, 2, 1]
-- |A010882: Cycle the numbers 1, 2, 3
a010882 :: Sequence
a010882 = Sequence $ cycle [1, 2, 3]
-- |A153727: Cycle the numbers 1, 4, 2
a153727 :: Sequence
a153727 = Sequence $ cycle [1, 4, 2]
-- |A080425: Cycle the numbers 0, 2, 1
a080425 :: Sequence
a080425 = Sequence $ cycle [0, 2, 1]
-- |A144437: Cycle the numbers 3, 3, 1
a144437 :: Sequence
a144437 = Sequence $ cycle [3, 3, 1]
-- |A131713: Cycle the numbers 1, -2, 1
a131713 :: Sequence
a131713 = Sequence $ cycle [1, -2, 1]
-- |A130784: Cycle the numbers 1, 3, 2
a130784 :: Sequence
a130784 = Sequence $ cycle [1, 3, 2]
-- |A169609: Cycle the numbers 1, 3, 3
a169609 :: Sequence
a169609 = Sequence $ cycle [1, 3, 3]
-- |A131561: Cycle the numbers 1, 1, -1
a131561 :: Sequence
a131561 = Sequence $ cycle [1, 1, -1]
-- |A052901: Cycle the numbers 3, 2, 2
a052901 :: Sequence
a052901 = Sequence $ cycle [3, 2, 2]
-- |A274339: Cycle the numbers 15, 24, 18
a274339 :: Sequence
a274339 = Sequence $ cycle [15, 24, 18]
-- |A073636: Cycle the numbers 1, 8, 9
a073636 :: Sequence
a073636 = Sequence $ cycle [1, 8, 9]
-- |A101000: Cycle the numbers 0, 1, 3
a101000 :: Sequence
a101000 = Sequence $ cycle [0, 1, 3]
-- |A131598: Cycle the numbers 2, 5, 8
a131598 :: Sequence
a131598 = Sequence $ cycle [2, 5, 8]
-- |A177702: Cycle the numbers 1, 1, 2
a177702 :: Sequence
a177702 = Sequence $ cycle [1, 1, 2]
-- |A131756: Cycle the numbers 2, -1, 3
a131756 :: Sequence
a131756 = Sequence $ cycle [2, -1, 3]
-- |A132677: Cycle the numbers 1, 2, -3
a132677 :: Sequence
a132677 = Sequence $ cycle [1, 2, -3]
-- |A146325: Cycle the numbers 1, 4, 1
a146325 :: Sequence
a146325 = Sequence $ cycle [1, 4, 1]
-- |A173259: Cycle the numbers 4, 1, 4
a173259 :: Sequence
a173259 = Sequence $ cycle [4, 1, 4]
-- |A164360: Cycle the numbers 5, 4, 3
a164360 :: Sequence
a164360 = Sequence $ cycle [5, 4, 3]
-- |A079978: Is n a multiple of three?
a079978 :: Sequence
a079978 = Sequence $ cycle [1, 0, 0]
-- |A000009: Number of 2-regular partitions of n
a000009 :: Sequence
a000009 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 2
-- |A000726: Number of 3-regular partitions of n
a000726 :: Sequence
a000726 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 3
-- |A001935: Number of 4-regular partitions of n
a001935 :: Sequence
a001935 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 4
-- |A035959: Number of 5-regular partitions of n
a035959 :: Sequence
a035959 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 5
-- |A219601: Number of 6-regular partitions of n
a219601 :: Sequence
a219601 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 6
-- |A035985: Number of 7-regular partitions of n
a035985 :: Sequence
a035985 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 7
-- |A261775: Number of 8-regular partitions of n
a261775 :: Sequence
a261775 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 8
-- |A104502: Number of 9-regular partitions of n
a104502 :: Sequence
a104502 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 9
-- |A261776: Number of 10-regular partitions of n
a261776 :: Sequence
a261776 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 10
-- |A328545: Number of 11-regular partitions of n
a328545 :: Sequence
a328545 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 11
-- |A328546: Number of 12-regular partitions of n
a328546 :: Sequence
a328546 = Sequence $ eulerTransform $ ofPositive $ \n -> signum $ n `mod` 12
-- |A001970: Partitions of partitions
a001970 :: Sequence
a001970 = Sequence $ eulerTransform $ drop 1 $ IL.toList Rec.partition
-- |A034691: Euler transform of powers of two
a034691 :: Sequence
a034691 = Sequence $ eulerTransform $ scanl (*) 1 $ repeat 2
-- |A034899: Euler transform of powers of two without one
a034899 :: Sequence
a034899 = Sequence $ eulerTransform $ scanl (*) 2 $ repeat 2
-- |A166861: Euler transform of the Fibonacci numbers
a166861 :: Sequence
a166861 = Sequence $ eulerTransform fibonacci' where fibonacci' = 1 : 1 : zipWith (+) fibonacci' (drop 1 fibonacci')
-- |A000335: Euler transform of tetrahedral numbers
a000335 :: Sequence
a000335 = Sequence $ eulerTransform' $ ofPositive $ \n -> n * (n + 1) * (n + 2) `div` 6
-- |A005928: Euler transform of cycle -3, -3, -2
a005928 :: Sequence
a005928 = Sequence $ eulerTransform $ cycle [-3, -3, -2]
-- |A073592: Euler transform of negative integers
a073592 :: Sequence
a073592 = Sequence $ eulerTransform $ ofPositive negate
-- |A061256: Euler transform of the sums of divisors
a061256 :: Sequence
a061256 = Sequence $ eulerTransform $ ofPositive $ AF.sigma 1
-- |A061255: Euler transform of totient function
a061255 :: Sequence
a061255 = Sequence $ eulerTransform $ ofPositive AF.totient
-- |A000332: binomial(n, 4)
a000332 :: Sequence
a000332 = Sequence $ ofIndices $ \n -> binomial n 4
-- |A000391: Euler tranform of binomial(n, 4)
a000391 :: Sequence
a000391 = Sequence $ eulerTransform' $ drop 4 $ ofIndices $ \n -> binomial n 4
-- |A005043: Riordan numbers
a005043 :: Sequence
a005043 = Sequence riordan where riordan = 1 : 0 : zipWith (\(nm, np) (a1, a2) -> (nm * (3 * a1 + 2 * a2)) `div` np) (zip [1..] [3..]) (zip riordan (drop 1 riordan))
-- |A358451: Inverse Euler transform of the Riordan numbers
a358451 :: Sequence
a358451 = Sequence $ 1 : inverseEulerTransform (drop 1 riordan) where riordan = 1 : 0 : zipWith (\(nm, np) (a1, a2) -> (nm * (3 * a1 + 2 * a2)) `div` np) (zip [1..] [3..]) (zip riordan (drop 1 riordan))
-- |A061257: Euler transform of the Carmichael lambda function
a061257 :: Sequence
a061257 = Sequence $ eulerTransform $ ofPositive AF.carmichael
-- |A000389: binomial(n, 5)
a000389 :: Sequence
a000389 = Sequence $ ofIndices $ \n -> binomial n 5
-- |A000417: Euler tranform of binomial(n, 5)
a000417 :: Sequence
a000417 = Sequence $ eulerTransform' $ drop 5 $ ofIndices $ \n -> binomial n 5
-- |A000579: binomial(n, 6)
a000579 :: Sequence
a000579 = Sequence $ ofIndices $ \n -> binomial n 6
-- |A000428: Euler tranform of binomial(n, 5)
a000428 :: Sequence
a000428 = Sequence $ eulerTransform' $ drop 6 $ ofIndices $ \n -> binomial n 6
-- |A107895: Euler tranform of the factorials
a107895 :: Sequence
a107895 = Sequence $ eulerTransform $ drop 1 $ IL.toList Rec.factorial
-- |A030009: Euler tranform of the primes
a030009 :: Sequence
a030009 = Sequence $ eulerTransform $ map unPrime primes
-- |A092119: Euler tranform of the ruler function
a092119 :: Sequence
a092119 = Sequence $ eulerTransform $ ofPositive $ \n -> adicValuation 2 $ n * 2
-- |A051064: 3-ruler function
a051064 :: Sequence
a051064 = Sequence $ ofPositive $ \n -> adicValuation 3 $ n * 3
-- |A173241: Euler tranform of the 3-ruler function
a173241 :: Sequence
a173241 = Sequence $ eulerTransform $ ofPositive $ \n -> adicValuation 3 $ n * 3
-- |A261031: Euler tranform of the Lucas numbers
a261031 :: Sequence
a261031 = Sequence $ eulerTransform lucas' where lucas' = 1 : 3 : zipWith (+) lucas' (drop 1 lucas')
-- |A030012: Euler tranform of one and the primes
a030012 :: Sequence
a030012 = Sequence $ eulerTransform' $ 1 : map unPrime primes
-- |A030010: Inverse Euler tranform of the primes
a030010 :: Sequence
a030010 = Sequence $ inverseEulerTransform $ map unPrime primes
-- |A320779: Inverse Euler transform of the number of divisors function
a320779 :: Sequence
a320779 = Sequence $ inverseEulerTransform $ ofPositive AF.divisorCount
-- |A320781: Inverse Euler transform of the Möbius function
a320781 :: Sequence
a320781 = Sequence $ inverseEulerTransform $ ofPositive $ AF.runMoebius . AF.moebius
-- |A320780: Inverse Euler transform of the sums of divisors
a320780 :: Sequence
a320780 = Sequence $ inverseEulerTransform $ ofPositive $ AF.sigma 1
-- |A320778: Inverse Euler transform of the totient function
a320778 :: Sequence
a320778 = Sequence $ 1 : inverseEulerTransform (ofPositive AF.totient)
-- |A085686: Inverse Euler transform of Bell numbers
a085686 :: Sequence
a085686 = Sequence $ inverseEulerTransform $ drop 1 bellNumbers
-- |A030011: Inverse Euler transform of one and the primes
a030011 :: Sequence
a030011 = Sequence $ inverseEulerTransform $ 1 : map unPrime primes
-- |A112354: Inverse Euler transform of the factorials
a112354 :: Sequence
a112354 = Sequence $ inverseEulerTransform $ drop 1 $ IL.toList Rec.factorial
-- |A320776: Inverse Euler transform of the number of prime divisors with multiplicity
a320776 :: Sequence
a320776 = Sequence $ 1 : inverseEulerTransform (ofPositive $ fromIntegral . AF.bigOmega)
-- |A144067: Euler transform of powers of three without one
a144067 :: Sequence
a144067 = Sequence $ eulerTransform $ scanl (*) 3 $ repeat 3
-- |A144068: Euler transform of powers of four without one
a144068 :: Sequence
a144068 = Sequence $ eulerTransform $ scanl (*) 4 $ repeat 4
-- |A144069: Euler transform of powers of five without one
a144069 :: Sequence
a144069 = Sequence $ eulerTransform $ scanl (*) 5 $ repeat 5
-- |A144070: Euler transform of powers of six without one
a144070 :: Sequence
a144070 = Sequence $ eulerTransform $ scanl (*) 6 $ repeat 6
-- |A144071: Euler transform of powers of seven without one
a144071 :: Sequence
a144071 = Sequence $ eulerTransform $ scanl (*) 7 $ repeat 7
-- |A144072: Euler transform of powers of eight without one
a144072 :: Sequence
a144072 = Sequence $ eulerTransform $ scanl (*) 8 $ repeat 8
-- |A144073: Euler transform of powers of nine without one
a144073 :: Sequence
a144073 = Sequence $ eulerTransform $ scanl (*) 9 $ repeat 9
-- |A292837: Euler transform of powers of ten without one
a292837 :: Sequence
a292837 = Sequence $ eulerTransform $ scanl (*) 10 $ repeat 10
-- |A065958: psi-2 function
a065958 :: Sequence
a065958 = Sequence $ ofPositive $ generalizedPsi 2
-- |A065959: psi-3 function
a065959 :: Sequence
a065959 = Sequence $ ofPositive $ generalizedPsi 3
-- |A065960: psi-4 function
a065960 :: Sequence
a065960 = Sequence $ ofPositive $ generalizedPsi 4
-- |A351300: psi-5 function
a351300 :: Sequence
a351300 = Sequence $ ofPositive $ generalizedPsi 5
-- |A351301: psi-6 function
a351301 :: Sequence
a351301 = Sequence $ ofPositive $ generalizedPsi 6
-- |A351302: psi-7 function
a351302 :: Sequence
a351302 = Sequence $ ofPositive $ generalizedPsi 7
-- |A351303: psi-8 function
a351303 :: Sequence
a351303 = Sequence $ ofPositive $ generalizedPsi 8
-- |A351304: psi-9 function
a351304 :: Sequence
a351304 = Sequence $ ofPositive $ generalizedPsi 9
-- |A351305: psi-10 function
a351305 :: Sequence
a351305 = Sequence $ ofPositive $ generalizedPsi 10
-- |A301978: Euler transform of the psi-2 function
a301978 :: Sequence
a301978 = Sequence $ eulerTransform $ ofPositive $ generalizedPsi 2
-- |A061159: Numerators of the Euler transform of always 1/2
a061159 :: Sequence
a061159 = Sequence $ map numerator $ eulerTransformG $ repeat $ 1 % 2
-- |A061160: Numerators of the Euler transform of always 1/3
a061160 :: Sequence
a061160 = Sequence $ map numerator $ eulerTransformG $ repeat $ 1 % 3
-- |A061161: Numerators of the Euler transform of always 1/4
a061161 :: Sequence
a061161 = Sequence $ map numerator $ eulerTransformG $ repeat $ 1 % 4
-- |A261047: Euler tranform of the factorials from two
a261047 :: Sequence
a261047 = Sequence $ eulerTransform $ drop 2 $ IL.toList Rec.factorial
-- |A290351: Euler transform of Bell numbers
a290351 :: Sequence
a290351 = Sequence $ eulerTransform $ drop 1 bellNumbers
-- |A000045: Fibonacci numbers
a000045 :: Sequence
a000045 = Sequence $ nBonacci 2
-- |A000073: Tribonacci numbers
a000073 :: Sequence
a000073 = Sequence $ nBonacci 3
-- |A000078: Tetranacci numbers
a000078 :: Sequence
a000078 = Sequence $ nBonacci 4
-- |A001591: Pentanacci numbers
a001591 :: Sequence
a001591 = Sequence $ nBonacci 5
-- |A001592: Hexanacci numbers
a001592 :: Sequence
a001592 = Sequence $ nBonacci 6
-- |A122189: Heptanacci numbers
a122189 :: Sequence
a122189 = Sequence $ nBonacci 7
-- |A079262: Octanacci numbers
a079262 :: Sequence
a079262 = Sequence $ nBonacci 8
-- |A055457: 5-ruler function
a055457 :: Sequence
a055457 = Sequence $ ofPositive $ \n -> adicValuation 5 $ n * 5
-- |A373296: Euler tranform of the 5-ruler function
a373296 :: Sequence
a373296 = Sequence $ eulerTransform $ ofPositive $ \n -> adicValuation 5 $ n * 5
-- |A373217: 7-ruler function
a373217 :: Sequence
a373217 = Sequence $ ofPositive $ \n -> adicValuation 7 $ n * 7
-- |A373298: Euler tranform of the 7-ruler function
a373298 :: Sequence
a373298 = Sequence $ eulerTransform $ ofPositive $ \n -> adicValuation 7 $ n * 7
-- |A057427: A zero and then always one
a057427 :: Sequence
a057427 = Sequence $ 0 : repeat 1
-- |A000296: Set partitions without singletons
a000296 :: Sequence
a000296 = Sequence $ inverseBinomialTransform bellNumbers
-- |A000111: Up/down numbers
a000111 :: Sequence
a000111 = Sequence $ egf $ (1 + s) / c where (s, c) = sinCosR X
-- |A000364: Secant numbers
a000364 :: Sequence
a000364 = Sequence $ evens $ egf $ 1 / c where (_, c) = sinCosR X
-- |A000182: Tangent numbers
a000182 :: Sequence
a000182 = Sequence $ odds $ egf $ s / c where (s, c) = sinCosR X
-- |A000587: Complementary Bell numbers
a000587 :: Sequence
a000587 = Sequence $ ofIndices $ \n -> sum $ zipWith (*) (Rec.stirling2 `infiniteIndex` n) (cycle [1, -1])
-- |A000248: Sequence with EGF exp(x * exp(x))
a000248 :: Sequence
a000248 = Sequence $ egf $ expR $ X * expR X
-- |A000258: Number of pairs of set partitions where the first is finer than the second
a000258 :: Sequence
a000258 = Sequence $ ofIndices (\n -> sum $ zipWith (*) (Rec.stirling2 `infiniteIndex` n) bellNumbers)
-- |A006252: Sequence with EGF 1/(1 - log(1 + x))
a006252 :: Sequence
a006252 = Sequence $ egf $ recip $ 1 - logR (1 + X)
-- |A024429: Sequence with EGF sinh(exp(x) - 1)
a024429 :: Sequence
a024429 = Sequence $ egf s where (s, _) = sinhCoshR $ expR X - 1
-- |A002741: Logarithmic numbes
a002741 :: Sequence
a002741 = Sequence $ egf $ negate (logR $ 1 - X) * expR (negate X)
-- |A009116: Sequence with EGF cos(x)/exp(x)
a009116 :: Sequence
a009116 = Sequence $ egf $ c / expR X where (_, c) = sinCosR X
-- |A094088: Sequence with EGF 1/(2 - cosh(x))
a094088 :: Sequence
a094088 = Sequence $ evens $ egf $ recip $ 2 - c where (_, c) = sinhCoshR X
-- |A005493: 2-Bell numbers
a005493 :: Sequence
a005493 = Sequence $ binomialTransform $ drop 1 bellNumbers
-- |A005494: 3-Bell numbers
a005494 :: Sequence
a005494 = Sequence $ nTimes 2 binomialTransform $ drop 1 bellNumbers
-- |A045379: 4-Bell numbers
a045379 :: Sequence
a045379 = Sequence $ nTimes 3 binomialTransform $ drop 1 bellNumbers
-- |A196834: 5-Bell numbers
a196834 :: Sequence
a196834 = Sequence $ nTimes 4 binomialTransform $ drop 1 bellNumbers
-- |A000925: Number of ordered partitions of n into 2 squares
a000925 :: Sequence
a000925 = Sequence $ ofIndices $ \n -> genericLength $ filter isSquare [n - k * k | k <- [0..intSquareRoot n]]
-- |A003415: Arithmetic derivative
a003415 :: Sequence
a003415 = Sequence $ ofIndices $ makeArithmeticDerivative $ const 1
-- |A068720: Arithmetic derivative of the squares
a068720 :: Sequence
a068720 = Sequence $ zipWith (\n n' -> 2 * n * n') [1..] $ ofPositive $ makeArithmeticDerivative $ const 1
-- |A068719: Arithmetic derivative of the even numbers
a068719 :: Sequence
a068719 = Sequence $ zipWith (\n n' -> n + 2 * n') [1..] $ ofPositive $ makeArithmeticDerivative $ const 1
-- |A068721: Arithmetic derivative of the cubes
a068721 :: Sequence
a068721 = Sequence $ zipWith (\n n' -> 3 * n * n * n') [1..] $ ofPositive $ makeArithmeticDerivative $ const 1
-- |A068346: Second arithmetic derivative
a068346 :: Sequence
a068346 = Sequence $ ofIndices $ nTimes 2 $ makeArithmeticDerivative $ const 1
-- |A099306: Third arithmetic derivative
a099306 :: Sequence
a099306 = Sequence $ ofIndices $ nTimes 3 $ makeArithmeticDerivative $ const 1
-- |A258644: Fourth arithmetic derivative
a258644 :: Sequence
a258644 = Sequence $ ofIndices $ nTimes 4 $ makeArithmeticDerivative $ const 1
-- |A258645: Fifth arithmetic derivative
a258645 :: Sequence
a258645 = Sequence $ ofIndices $ nTimes 5 $ makeArithmeticDerivative $ const 1
-- |A258646: Sixth arithmetic derivative
a258646 :: Sequence
a258646 = Sequence $ ofIndices $ nTimes 6 $ makeArithmeticDerivative $ const 1
-- |A258647: Seventh arithmetic derivative
a258647 :: Sequence
a258647 = Sequence $ ofIndices $ nTimes 7 $ makeArithmeticDerivative $ const 1
-- |A258648: Eighth arithmetic derivative
a258648 :: Sequence
a258648 = Sequence $ ofIndices $ nTimes 8 $ makeArithmeticDerivative $ const 1
-- |A258649: Ninth arithmetic derivative
a258649 :: Sequence
a258649 = Sequence $ ofIndices $ nTimes 9 $ makeArithmeticDerivative $ const 1
-- |A258650: Tenth arithmetic derivative
a258650 :: Sequence
a258650 = Sequence $ ofIndices $ nTimes 10 $ makeArithmeticDerivative $ const 1
-- |A258851: Pi-based arithmetic derivative
a258851 :: Sequence
a258851 = Sequence $ ofIndices $ makeArithmeticDerivative $ primeCount . unPrime
-- |A007395: Always two
a007395 :: Sequence
a007395 = Sequence $ repeat 2
-- |A010701: Always three
a010701 :: Sequence
a010701 = Sequence $ repeat 3
-- |A010716: Always five
a010716 :: Sequence
a010716 = Sequence $ repeat 5
-- |A010722: Always six
a010722 :: Sequence
a010722 = Sequence $ repeat 6
-- |A010727: Always seven
a010727 :: Sequence
a010727 = Sequence $ repeat 7
-- |A010731: Always eight
a010731 :: Sequence
a010731 = Sequence $ repeat 8
-- |A010734: Always nine
a010734 :: Sequence
a010734 = Sequence $ repeat 9
-- |A010692: Always ten
a010692 :: Sequence
a010692 = Sequence $ repeat 10
-- |A010850: Always 11
a010850 :: Sequence
a010850 = Sequence $ repeat 11
-- |A010851: Always 12
a010851 :: Sequence
a010851 = Sequence $ repeat 12
-- |A010852: Always 13
a010852 :: Sequence
a010852 = Sequence $ repeat 13
-- |A010853: Always 14
a010853 :: Sequence
a010853 = Sequence $ repeat 14
-- |A010854: Always 15
a010854 :: Sequence
a010854 = Sequence $ repeat 15
-- |A010855: Always 16
a010855 :: Sequence
a010855 = Sequence $ repeat 16
-- |A010856: Always 17
a010856 :: Sequence
a010856 = Sequence $ repeat 17
-- |A010857: Always 18
a010857 :: Sequence
a010857 = Sequence $ repeat 18
-- |A010858: Always 19
a010858 :: Sequence
a010858 = Sequence $ repeat 19
-- |A010859: Always 20
a010859 :: Sequence
a010859 = Sequence $ repeat 20
-- |A010860: Always 21
a010860 :: Sequence
a010860 = Sequence $ repeat 21
-- |A010861: Always 22
a010861 :: Sequence
a010861 = Sequence $ repeat 22
-- |A010862: Always 23
a010862 :: Sequence
a010862 = Sequence $ repeat 23
-- |A010863: Always 24
a010863 :: Sequence
a010863 = Sequence $ repeat 24
-- |A010864: Always 25
a010864 :: Sequence
a010864 = Sequence $ repeat 25
-- |A010865: Always 26
a010865 :: Sequence
a010865 = Sequence $ repeat 26
-- |A010866: Always 27
a010866 :: Sequence
a010866 = Sequence $ repeat 27
-- |A010867: Always 28
a010867 :: Sequence
a010867 = Sequence $ repeat 28
-- |A010868: Always 29
a010868 :: Sequence
a010868 = Sequence $ repeat 29
-- |A010869: Always 30
a010869 :: Sequence
a010869 = Sequence $ repeat 30
-- |A010870: Always 31
a010870 :: Sequence
a010870 = Sequence $ repeat 31
-- |A010871: Always 32
a010871 :: Sequence
a010871 = Sequence $ repeat 32
-- |A040000: A one and then always two
a040000 :: Sequence
a040000 = Sequence $ 1 : repeat 2
-- |A040002: A two and then always four
a040002 :: Sequence
a040002 = Sequence $ 2 : repeat 4
-- |A040006: A three and then always six
a040006 :: Sequence
a040006 = Sequence $ 3 : repeat 6
-- |A040012: A four and then always eight
a040012 :: Sequence
a040012 = Sequence $ 4 : repeat 8
-- |A040020: A five and then always ten
a040020 :: Sequence
a040020 = Sequence $ 5 : repeat 10
-- |A040030: A six and then always 12
a040030 :: Sequence
a040030 = Sequence $ 6 : repeat 12
-- |A040042: A seven and then always 14
a040042 :: Sequence
a040042 = Sequence $ 7 : repeat 14
-- |A040056: An eight and then always 16
a040056 :: Sequence
a040056 = Sequence $ 8 : repeat 16
-- |A040072: A nine and then always 18
a040072 :: Sequence
a040072 = Sequence $ 9 : repeat 18
-- |A040090: A ten and then always 20
a040090 :: Sequence
a040090 = Sequence $ 10 : repeat 20
-- |A040110: A 11 and then always 22
a040110 :: Sequence
a040110 = Sequence $ 11 : repeat 22
-- |A040132: A 12 and then always 24
a040132 :: Sequence
a040132 = Sequence $ 12 : repeat 24
-- |A040156: A 13 and then always 26
a040156 :: Sequence
a040156 = Sequence $ 13 : repeat 26
-- |A040182: A 14 and then always 28
a040182 :: Sequence
a040182 = Sequence $ 14 : repeat 28
-- |A040210: A 15 and then always 30
a040210 :: Sequence
a040210 = Sequence $ 15 : repeat 30
-- |A040240: A 16 and then always 32
a040240 :: Sequence
a040240 = Sequence $ 16 : repeat 32
-- |A040272: A 17 and then always 34
a040272 :: Sequence
a040272 = Sequence $ 17 : repeat 34
-- |A040306: A 18 and then always 36
a040306 :: Sequence
a040306 = Sequence $ 18 : repeat 36
-- |A040342: A 19 and then always 38
a040342 :: Sequence
a040342 = Sequence $ 19 : repeat 38
-- |A040380: A 20 and then always 40
a040380 :: Sequence
a040380 = Sequence $ 20 : repeat 40
-- |A040420: A 21 and then always 42
a040420 :: Sequence
a040420 = Sequence $ 21 : repeat 42
-- |A040462: A 22 and then always 44
a040462 :: Sequence
a040462 = Sequence $ 22 : repeat 44
-- |A040506: A 23 and then always 46
a040506 :: Sequence
a040506 = Sequence $ 23 : repeat 46
-- |A040552: A 24 and then always 48
a040552 :: Sequence
a040552 = Sequence $ 24 : repeat 48
-- |A040600: A 25 and then always 50
a040600 :: Sequence
a040600 = Sequence $ 25 : repeat 50
-- |A040650: A 26 and then always 52
a040650 :: Sequence
a040650 = Sequence $ 26 : repeat 52
-- |A040702: A 27 and then always 54
a040702 :: Sequence
a040702 = Sequence $ 27 : repeat 54
-- |A040756: A 28 and then always 56
a040756 :: Sequence
a040756 = Sequence $ 28 : repeat 56
-- |A040812: A 29 and then always 58
a040812 :: Sequence
a040812 = Sequence $ 29 : repeat 58
-- |A040870: A 30 and then always 60
a040870 :: Sequence
a040870 = Sequence $ 30 : repeat 60
-- |A040930: A 31 and then always 62
a040930 :: Sequence
a040930 = Sequence $ 31 : repeat 62
-- |A255910: A one and then always seven
a255910 :: Sequence
a255910 = Sequence $ 1 : repeat 7
-- |A057428: A zero and then always negative one
a057428 :: Sequence
a057428 = Sequence $ 0 : repeat (-1)
-- |A157928: Two zeros and then always one
a157928 :: Sequence
a157928 = Sequence $ 0 : 0 : repeat 1
