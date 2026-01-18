{-# LANGUAGE PatternSynonyms, ViewPatterns #-}

module Lang0315.Util
( pattern (:>)
, pattern (:%)
, DivisiblePromise(..)
, (.:)
) where

import Data.List (unsnoc)
import Foreign.Storable
import Data.Ratio

{-# COMPLETE [], (:>) #-}
-- | Bidirectional pattern synonym for extracting the last element of a list.
pattern (:>) :: [a] -> a -> [a]
pattern xs :> x <- (unsnoc -> Just (xs, x))
  where xs :> x = xs ++ [x]
infixl 5 :>

{-# COMPLETE (:%) #-}
-- | Bidirectional pattern synonym for extracting the numerator and denominator of a 'Ratio'
pattern (:%) :: Integral a => a -> a -> Ratio a
pattern n :% d <- (liftA2 (,) numerator denominator -> (n, d))
  where n :% d = n % d
infixl 7 :%

-- | A newtype wrapper over an integral type that allows it to act like a 'Ratio', panicking if nonexact divisions are attempted.
newtype DivisiblePromise a = DivisiblePromise{ unDivisiblePromise :: a }
  deriving newtype (Num, Eq, Ord, Enum, Storable, Read, Show)

instance Integral a => Fractional (DivisiblePromise a) where
  fromRational (r :% 1) = DivisiblePromise $ fromIntegral r
  fromRational _ = error "DivisiblePromise: promise broken, fromRational with non-1 denominator"
  recip x@(DivisiblePromise 1) = x
  recip x@(DivisiblePromise (-1)) = x
  recip _ = error "DivisiblePromise: promise broken, recip with non-unit"
  (DivisiblePromise x) / (DivisiblePromise y)
    | x `mod` y == 0 = DivisiblePromise $ x `div` y
    | otherwise = error "DivsiblePromise: promise broken, x / y with x not a multiple of y"

instance Integral a => Real (DivisiblePromise a) where
  toRational = (% 1) . fromIntegral . unDivisiblePromise

instance Integral a => RealFrac (DivisiblePromise a) where
  properFraction = (, 0) . fromIntegral . unDivisiblePromise
  truncate = fromIntegral . unDivisiblePromise
  round = fromIntegral . unDivisiblePromise
  floor = fromIntegral . unDivisiblePromise
  ceiling = fromIntegral . unDivisiblePromise

-- | Composition for two-variable functions
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) f g a b = f $ g a b
