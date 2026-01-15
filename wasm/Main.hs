module Main (main) where

import Lang0315.Parser
import Lang0315.Interpreter
import Lang0315.Sequence

import GHC.Wasm.Prim
import Data.Functor
import Data.Coerce

foreign export javascript "hs_start" main :: IO ()
main :: IO ()
main = pure ()

foreign import javascript safe "await $1($2);" jsCallCallback :: JSVal -> JSVal -> IO ()
foreign import javascript unsafe "return undefined;" jsUndefined :: JSVal
foreign import javascript unsafe "return BigInt($1);" jsStringToBigInt :: JSString -> JSVal
foreign import javascript unsafe "return $1;" jsIntToVal :: Int -> JSVal
foreign import javascript unsafe "return [$1, $2];" jsMakePair :: JSVal -> JSVal -> JSVal

newtype JSArray = JSArray { unJSArray :: JSVal }

bamboozle :: [a] -> Bool
bamboozle [] = False
bamboozle _ = True
{-# NOINLINE bamboozle #-}

foreign import javascript unsafe "return [];" jsNil_ :: Bool -> JSArray
foreign import javascript unsafe "$1.push($2); return $1;" jsPush :: JSArray -> JSVal -> JSArray
foreign import javascript unsafe "return $1.length;" jsLength :: JSArray -> Int
foreign import javascript unsafe "return $1[$2];" jsAt :: JSArray -> Int -> JSVal

listToArray :: [JSVal] -> JSArray
listToArray xs = foldl' jsPush (jsNil_ $ bamboozle xs) xs

arrayToList :: JSArray -> [JSVal]
arrayToList arr = jsAt arr <$> [0..jsLength arr-1]

foreign export javascript "run" run :: Int -> JSVal -> JSString -> JSString -> IO JSVal
run l cb path' code' = let
  path = fromJSString path'
  code = fromJSString code'
  in case parseMany path code of
    Left err -> pure $ coerce $ toJSString err
    Right expr -> case runContext [] $ mapM interpret expr of
      (Left err, _) -> pure $ coerce $ toJSString err
      (Right [], _) -> pure $ coerce $ toJSString "Empty file!"
      (Right ss, _) -> mapM_ (jsCallCallback cb . jsStringToBigInt . toJSString . show) (take l $ unSequence $ last ss) $> jsUndefined

foreign export javascript "sequences" jsSequences :: JSArray
jsSequences = listToArray $ map (\(i, (_, desc)) -> jsMakePair (jsIntToVal $ fromIntegral i) (coerce $ toJSString desc)) sequences
