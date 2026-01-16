module Lang0315.Interpreter
( interpret
, Context
, runContext
, sequences
) where

import Lang0315.Parser (Expr(..))
import Lang0315.Sequence

import Numeric.Natural
import Control.Monad.State
import Control.Monad.Except

sequences :: [(Natural, (Sequence, String))]
sequences =
  [ (000012, (a000012, "Always one"))
  , (001477, (a001477, "Nonnegative integers"))
  , (000027, (a000027, "Positive integers"))
  , (000040, (a000040, "Prime numbers"))
  , (000045, (a000045, "Fibonacci numbers"))
  , (000203, (a000203, "Sum of the divisors of n"))
  , (000005, (a000005, "Number of divisors of n"))
  , (000217, (a000217, "Triangular numbers"))
  , (000010, (a000010, "Euler totient function"))
  , (000108, (a000108, "Catalan numbers"))
  , (000041, (a000041, "Number of partitions of n"))
  , (000290, (a000290, "Square numbers"))
  , (001222, (a001222, "Number of prime divisors of n counted with multiplicity"))
  , (000142, (a000142, "Factorial numbers"))
  , (001221, (a001221, "Number of distinct primes dividing n"))
  , (000720, (a000720, "Number of primes <= n"))
  , (007318, (a007318, "Pascal's triangle read by rows"))
  , (000120, (a000120, "Number of ones in binary expansion of n"))
  , (005117, (a005117, "Squarefree numbers"))
  , (002110, (a002110, "Primorial numbers"))
  , (001622, (a001622, "Decimal expansion of golden ratio "))
  , (001358, (a001358, "Semiprimes"))
  , (008683, (a008683, "Möbius function"))
  , (000032, (a000032, "Lucas numbers beginning at 2"))
  , (000225, (a000225, "2^n - 1"))
  , (000110, (a000110, "Bell or exponential numbers"))
  , (005408, (a005408, "The odd numbers"))
  , (002275, (a002275, "Repunits: (10^n - 1)/9"))
  , (006530, (a006530, "Greatest prime dividing n"))
  , (000007, (a000007, "An one and then always zero"))
  , (000796, (a000796, "Decimal expansion of pi"))
  , (000961, (a000961, "Powers of primes"))
  , (000984, (a000984, "Central binomial coefficients"))
  , (000578, (a000578, "Cube numbers"))
  , (002808, (a002808, "The composite numbers"))
  , (020639, (a020639, "Least prime dividing n"))
  , (000244, (a000244, "Powers of three"))
  , (070939, (a070939, "Length of binary representation of n"))
  , (000292, (a000292, "Tetrahedral numbers"))
  , (002113, (a002113, "Palindromes in base 10"))
  , (000129, (a000129, "Pell numbers"))
  , (005843, (a005843, "The nonnegative even numbers"))
  , (000035, (a000035, "Parity of n"))
  , (001045, (a001045, "Jacobsthal sequence"))
  , (001113, (a001113, "Decimal expansion of e"))
  , (000396, (a000396, "Perfect numbers k"))
  , (000043, (a000043, "Mersenne exponents"))
  , (001764, (a001764, "binomial(3*n,n)/(2*n+1)"))
  , (001147, (a001147, "Double factorial of odd numbers"))
  , (008277, (a008277, "Triangle of Stirling numbers of the second kind"))
  , (000312, (a000312, "n^n"))
  , (000302, (a000302, "Powers of four"))
  , (000670, (a000670, "Fubini numbers"))
  , (001006, (a001006, "Motzkin numbers"))
  , (010060, (a010060, "Thue-Morse sequence"))
  , (001065, (a001065, "Sum of proper divisors of n"))
  , (055642, (a055642, "Number of digits in the decimal expansion of n"))
  , (000079, (a000079, "Powers of two"))
  , (100995, (a100995, "If n is a prime power p^m, m >= 1, then m, otherwise 0"))
  , (014963, (a014963, "Exponential of Mangoldt function M(n)"))
  , (023443, (a023443, "Numbers from negative one"))
  , (000326, (a000326, "Pentagonal numbers"))
  , (000166, (a000166, "Number of derangements"))
  , (000330, (a000330, "Square pyramidal numbers"))
  , (002620, (a002620, "Quarter-squares"))
  , (001511, (a001511, "The ruler function"))
  , (004526, (a004526, "Nonnegative integers repeated"))
  , (000085, (a000085, "Number of self-inverse permutations on n letters"))
  , (001227, (a001227, "Number of odd divisors"))
  , (001906, (a001906, "Bisection of Fibonacci sequence"))
  , (000124, (a000124, "Central polygonal numbers"))
  , (001405, (a001405, "Binomial(n, floor(n/2))"))
  , (000583, (a000583, "Fourth powers"))
  , (018252, (a018252, "Nonprime numbers"))
  , (001157, (a001157, "Sum of squares of divisors of n"))
  , (001700, (a001700, "binomial(2*n+1, n+1)"))
  , (008292, (a008292, "Triangle of Eulerian numbers"))
  , (005101, (a005101, "Abundant numbers"))
  , (001615, (a001615, "Dedekind psi function"))
  , (003418, (a003418, "Least Common Multiple"))
  , (000169, (a000169, "Number of labeled rooted trees with n nodes"))
  , (246655, (a246655, "Prime powers"))
  , (027641, (a027641, "Numerator of Bernoulli number"))
  , (027642, (a027642, "Denominator of Bernoulli number"))
  , (000272, (a000272, "Number of trees on n labeled nodes"))
  , (000004, (a000004, "Always zero"))
  , (000204, (a000204, "Lucas numbers"))
  , (000069, (a000069, "Odious numbers"))
  , (002322, (a002322, "Reduced totient function"))
  , (001969, (a001969, "Evil numbers"))
  , (000002, (a000002, "Kolakoski sequence"))
  , (003056, (a003056, "Inverse of triangular numbers"))
  , (000593, (a000593, "Sum of odd divisors of n"))
  , (001097, (a001097, "Twin primes"))
  , (006882, (a006882, "Double factorials"))
  , (011557, (a011557, "Powers of ten"))
  , (000262, (a000262, "Number of sets of lists"))
  , (005811, (a005811, "Number of runs in binary expansion of n"))
  , (144944, (a144944, "Super-Catalan triangle"))
  , (001003, (a001003, "Schroeder's second problem"))
  , (000196, (a000196, "Integer part of square root of n"))
  , (001481, (a001481, "Sum of 2 squares"))
  , (005100, (a005100, "Deficient numbers"))
  , (001037, (a001037, "Number of degree-n irreducible polynomials over GF(2)"))
  , (000594, (a000594, "Ramanujan's tau function"))
  , (000688, (a000688, "Number of Abelian groups of order n"))
  , (000001, (a000001, "Number of groups of order n"))
  , (000031, (a000031, "Number of n-bead necklaces with 2 colors when turning over is not allowed"))
  , (000058, (a000058, "Sylvester's sequence"))
  , (008279, (a008279, "Triangle T(n,k) = n!/(n-k)!, read by rows"))
  , (001057, (a001057, "Canonical enumeration of integers"))
  , (000161, (a000161, "Number of partitions of n into 2 squares"))
  , (001489, (a001489, "Nonpositive integers"))
  , (001478, (a001478, "Negative integers"))
  , (022958, (a022958, "2-n"))
  , (022996, (a022996, "40-n"))
  , (109613, (a109613, "Odd numbers repeated twice"))
  , (008585, (a008585, "Multiples of three"))
  , (069074, (a069074, "(2*n+2)*(2*n+3)*(2*n+4)"))
  , (010709, (a010709, "Always four"))
  , (059841, (a059841, "Is n even?"))
  , (000034, (a000034, "Cycle the numbers 1, 2"))
  , (033999, (a033999, "Cycle the numbers 1, -1"))
  , (010684, (a010684, "Cycle the numbers 1, 3"))
  , (010685, (a010685, "Cycle the numbers 1, 4"))
  , (010673, (a010673, "Cycle the numbers 0, 2"))
  , (010674, (a010674, "Cycle the numbers 0, 3"))
  , (010688, (a010688, "Cycle the numbers 1, 7"))
  , (105397, (a105397, "Cycle the numbers 4, 2"))
  , (049347, (a049347, "Cycle the numbers 1, -1, 0"))
  , (011655, (a011655, "Cycle the numbers 0, 1, 1"))
  , (061347, (a061347, "Cycle the numbers 1, 1, -2"))
  , (102283, (a102283, "Cycle the numbers 0, 1, -1"))
  , (130196, (a130196, "Cycle the numbers 1, 2, 2"))
  , (131534, (a131534, "Cycle the numbers 1, 2, 1"))
  , (010882, (a010882, "Cycle the numbers 1, 2, 3"))
  , (153727, (a153727, "Cycle the numbers 1, 4, 2"))
  , (080425, (a080425, "Cycle the numbers 0, 2, 1"))
  , (144437, (a144437, "Cycle the numbers 3, 3, 1"))
  , (131713, (a131713, "Cycle the numbers 1, -2, 1"))
  , (130784, (a130784, "Cycle the numbers 1, 3, 2"))
  , (169609, (a169609, "Cycle the numbers 1, 3, 3"))
  , (131561, (a131561, "Cycle the numbers 1, 1, -1"))
  , (052901, (a052901, "Cycle the numbers 3, 2, 2"))
  , (274339, (a274339, "Cycle the numbers 15, 24, 18"))
  , (073636, (a073636, "Cycle the numbers 1, 8, 9"))
  , (101000, (a101000, "Cycle the numbers 0, 1, 3"))
  , (131598, (a131598, "Cycle the numbers 2, 5, 8"))
  , (177702, (a177702, "Cycle the numbers 1, 1, 2"))
  , (131756, (a131756, "Cycle the numbers 2, -1, 3"))
  , (132677, (a132677, "Cycle the numbers 1, 2, -3"))
  , (146325, (a146325, "Cycle the numbers 1, 4, 1"))
  , (173259, (a173259, "Cycle the numbers 4, 1, 4"))
  , (164360, (a164360, "Cycle the numbers 5, 4, 3"))
  , (079978, (a079978, "Is n a multiple of three?"))
  , (000009, (a000009, "Number of 2-regular partitions of n"))
  , (000726, (a000726, "Number of 3-regular partitions of n"))
  , (001935, (a001935, "Number of 4-regular partitions of n"))
  , (035959, (a035959, "Number of 5-regular partitions of n"))
  , (219601, (a219601, "Number of 6-regular partitions of n"))
  , (035985, (a035985, "Number of 7-regular partitions of n"))
  , (261775, (a261775, "Number of 8-regular partitions of n"))
  , (104502, (a104502, "Number of 9-regular partitions of n"))
  , (261776, (a261776, "Number of 10-regular partitions of n"))
  , (328545, (a328545, "Number of 11-regular partitions of n"))
  , (328546, (a328546, "Number of 12-regular partitions of n"))
  ]

type Context = ExceptT String (State [(String, Sequence)])

interpret :: Expr -> Context Sequence
interpret (ExprSequence i) = case lookup i sequences of
  Nothing -> throwError $ "Unknown sequence " ++ show i
  Just (s, _) -> pure s
interpret (ExprNegate r) = do r' <- interpret r; pure $ negate r'
interpret (ExprAbs r) = do r' <- interpret r; pure $ abs r'
interpret (ExprAdd l r) = do r' <- interpret r; l' <- interpret l; pure $ l' + r'
interpret (ExprSubtract l r) = do r' <- interpret r; l' <- interpret l; pure $ l' - r'
interpret (ExprMultiply l r) = do r' <- interpret r; l' <- interpret l; pure $ l' * r'
interpret (ExprDivide l r) = do r' <- interpret r; l' <- interpret l; pure $ l' `seqDiv` r'
interpret (ExprModulo l r) = do r' <- interpret r; l' <- interpret l; pure $ l' `seqMod` r'
interpret (ExprPower l r) = do r' <- interpret r; l' <- interpret l; pure $ l' `seqPow` r'
interpret (ExprEqual l r) = do r' <- interpret r; l' <- interpret l; pure $ seqBoolean (==) l' r'
interpret (ExprLess l r) = do r' <- interpret r; l' <- interpret l; pure $ seqBoolean (<) l' r'
interpret (ExprComma l r) = do r' <- interpret r; l' <- interpret l; pure $ seqUnTriangle l' r'
interpret (ExprSemi l r) = do r' <- interpret r; l' <- interpret l; pure $ seqUnSquare l' r'
interpret (ExprIndex l r) = do r' <- interpret r; l' <- interpret l; pure $ l' `seqIndex` r'
interpret (ExprKeep l r) = do r' <- interpret r; l' <- interpret l; pure $ l' `seqKeep` r'
interpret (ExprCharacter r) = do r' <- interpret r; pure $ seqCharacter r'
interpret (ExprCut r) = do r' <- interpret r; pure $ seqCut r'
interpret (ExprJoin l r) = do r' <- interpret r; l' <- interpret l; pure $ l' `seqJoin` r'
interpret (ExprName n) = do
  variables <- get
  case lookup n variables of
    Nothing -> throwError $ "Undefined variable `" ++ n ++ "`"
    Just s -> pure s
interpret (ExprAssign n v) = do
  v' <- interpret v
  modify ((n, v') :)
  pure v'
interpret ExprEmpty = pure $ Sequence []

runContext :: [(String, Sequence)] -> Context a -> (Either String a, [(String, Sequence)])
runContext i = flip runState i . runExceptT
