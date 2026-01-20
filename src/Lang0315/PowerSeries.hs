module Lang0315.PowerSeries
( PowerSeries(..)
, coefficients
, fromCoefficients
, scale
, diff
, int
, int'
, sqrt'
, pow
, pow'
, exp'
, log'
, sinCos
, sinCos'
, asin'
, acos'
, atan'
, (@!)
, inverse
, sinhCosh
, sinhCosh'
, asinh'
, acosh'
, atanh'
) where

import qualified Data.List.Infinite as IL
import Data.List.Infinite (Infinite(..), (...))

newtype PowerSeries a = PowerSeries { coefficients' :: Infinite a }

coefficients :: PowerSeries a -> [a]
coefficients = IL.toList . coefficients'

fromCoefficients :: Num a => [a] -> PowerSeries a
fromCoefficients = PowerSeries . flip IL.prependList (IL.repeat 0)

undef :: String -> a
undef msg = error $ "PowerSeries: undefined operation " ++ msg

instance Num a => Num (PowerSeries a) where
  (PowerSeries xs) + (PowerSeries ys) = PowerSeries $ IL.zipWith (+) xs ys
  (PowerSeries xs) - (PowerSeries ys) = PowerSeries $ IL.zipWith (-) xs ys
  (PowerSeries xs) * (PowerSeries ys) = PowerSeries $ multiply xs ys
  negate (PowerSeries xs) = PowerSeries $ IL.map negate xs
  abs = undef "abs"
  signum = undef "signum"
  fromInteger n = PowerSeries $ fromInteger n :< IL.repeat 0

instance (Eq a, Fractional a) => Fractional (PowerSeries a) where
  (PowerSeries xs) / (PowerSeries ys) = PowerSeries $ divide xs ys
  fromRational n = PowerSeries $ fromRational n :< IL.repeat 0

instance (Eq a, Floating a) => Floating (PowerSeries a) where
  pi = PowerSeries $ pi :< IL.repeat 0
  exp = exp' exp
  log = log' log
  sqrt = sqrt' sqrt
  sin = fst . sinCos
  cos = snd . sinCos
  tan x = s / c where (s, c) = sinCos x
  asin = asin' asin sqrt
  acos = acos' acos sqrt
  atan = atan' atan
  sinh = fst . sinhCosh
  cosh = snd . sinhCosh
  tanh x = s / c where (s, c) = sinhCosh x
  asinh = asinh' sinh sqrt
  acosh = acosh' cosh sqrt
  atanh = atanh' atanh

scale :: Num a => a -> PowerSeries a -> PowerSeries a
scale n (PowerSeries xs) = PowerSeries $ IL.map (n *) xs

multiply :: Num a => IL.Infinite a -> IL.Infinite a -> IL.Infinite a
multiply (x :< xs) ya@(y :< ys) = x * y :< IL.zipWith (+) (IL.map (x *) ys) (multiply xs ya)

divide :: (Eq a, Fractional a) => IL.Infinite a -> IL.Infinite a -> IL.Infinite a
divide (0 :< xs) (0 :< ys) = divide xs ys
divide _ (0 :< _) = error "PowerSeries: impossible division"
divide (x :< xs) (y :< ys) = zs where zs = x / y :< IL.map (/ y) (IL.zipWith (-) xs $ multiply zs ys)

diff :: Num a => PowerSeries a -> PowerSeries a
diff (PowerSeries (_ :< xs)) = PowerSeries $ IL.zipWith (\n x -> x * fromInteger n) (1...) xs

int :: Fractional a => a -> PowerSeries a -> PowerSeries a
int x0 (PowerSeries xs) = PowerSeries $ x0 :< IL.zipWith (\n x -> x / fromInteger n) (1...) xs

int' :: Fractional a => PowerSeries a -> PowerSeries a
int' = int 0

sqrt' :: Fractional a => (a -> a) -> PowerSeries a -> PowerSeries a
sqrt' f0 (PowerSeries (x :< xs)) = let
  y = f0 x
  ys = IL.map (/(y + y)) (IL.zipWith (-) xs $ 0 :< multiply ys ys)
  in PowerSeries $ y :< ys

pow' :: (Eq a, Fractional a) => (a -> a -> a) -> a -> PowerSeries a -> PowerSeries a
pow' f0 e x@(PowerSeries (x0 :< _)) = let
  x' = diff x
  y' = scale e $ y * (x' / x)
  y = int (x0 `f0` e) y'
  in y

pow :: (Eq a, Floating a) => a -> PowerSeries a -> PowerSeries a
pow = pow' (**)

exp' :: (Eq a, Fractional a) => (a -> a) -> PowerSeries a -> PowerSeries a
exp' f0 x@(PowerSeries (x0 :< _)) = let
  x' = diff x
  y' = y * x'
  y = int (f0 x0) y'
  in y

log' :: (Eq a, Fractional a) => (a -> a) -> PowerSeries a -> PowerSeries a
log' f0 x@(PowerSeries (x0 :< _)) = let
  x' = diff x
  y' = x' / x
  y = int (f0 x0) y'
  in y

sinCos' :: (Eq a, Fractional a) => (a -> (a, a)) -> PowerSeries a -> (PowerSeries a, PowerSeries a)
sinCos' f0 x@(PowerSeries (x0 :< _)) = let
  (s0, c0) = f0 x0
  x' = diff x
  s' = c * x'
  c' = negate $ s * x'
  s = int s0 s' 
  c = int c0 c'
  in (s, c)

sinCos :: (Eq a, Floating a) => PowerSeries a -> (PowerSeries a, PowerSeries a)
sinCos = sinCos' $ liftA2 (,) sin cos

asin' :: (Eq a, Floating a) => (a -> a) -> (a -> a) -> PowerSeries a -> PowerSeries a
asin' f0 sqrt0 x@(PowerSeries (x0 :< _)) = let
  x' = diff x
  y' = x' / sqrt' sqrt0 (1 - x * x)
  y = int (f0 x0) y'
  in y

acos' :: (Eq a, Floating a) => (a -> a) -> (a -> a) -> PowerSeries a -> PowerSeries a
acos' = asin' -- Same DE, different initial conditions

atan' :: (Eq a, Floating a) => (a -> a) -> PowerSeries a -> PowerSeries a
atan' f0 x@(PowerSeries (x0 :< _)) = let
  x' = diff x
  y' = x' / (1 + x * x)
  y = int (f0 x0) y'
  in y

compose :: (Eq a, Num a) => Infinite a -> Infinite a -> Infinite a
compose (x :< xs) ya@(0 :< ys) = x :< multiply ys (compose xs ya)
compose _ _ = error "PowerSeries: impossible composition"

infixr 9 @!
(@!) :: (Eq a, Num a) => PowerSeries a -> PowerSeries a -> PowerSeries a
(PowerSeries xs) @! (PowerSeries ys) = PowerSeries $ compose xs ys

invert :: (Eq a, Fractional a) => Infinite a -> Infinite a
invert (0 :< xs) = ys where ys = 0 :< divide (1 :< IL.repeat 0) (compose xs ys)
invert _ = error "PowerSeries: impossible inverse"

inverse :: (Eq a, Fractional a) => PowerSeries a -> PowerSeries a
inverse (PowerSeries xs) = PowerSeries $ invert xs

sinhCosh' :: (Eq a, Fractional a) => (a -> (a, a)) -> PowerSeries a -> (PowerSeries a, PowerSeries a)
sinhCosh' f0 x@(PowerSeries (x0 :< _)) = let
  (s0, c0) = f0 x0
  x' = diff x
  s' = c * x'
  c' = s * x'
  s = int s0 s' 
  c = int c0 c'
  in (s, c)

sinhCosh :: (Eq a, Floating a) => PowerSeries a -> (PowerSeries a, PowerSeries a)
sinhCosh = sinhCosh' $ liftA2 (,) sinh cosh

asinh' :: (Eq a, Floating a) => (a -> a) -> (a -> a) -> PowerSeries a -> PowerSeries a
asinh' f0 sqrt0 x@(PowerSeries (x0 :< _)) = let
  x' = diff x
  y' = x' / sqrt' sqrt0 (x * x + 1)
  y = int (f0 x0) y'
  in y

acosh' :: (Eq a, Floating a) => (a -> a) -> (a -> a) -> PowerSeries a -> PowerSeries a
acosh' f0 sqrt0 x@(PowerSeries (x0 :< _)) = let
  x' = diff x
  y' = x' / sqrt' sqrt0 (x * x - 1)
  y = int (f0 x0) y'
  in y

atanh' :: (Eq a, Floating a) => (a -> a) -> PowerSeries a -> PowerSeries a
atanh' f0 x@(PowerSeries (x0 :< _)) = let
  x' = diff x
  y' = x' / (1 - x * x)
  y = int (f0 x0) y'
  in y
