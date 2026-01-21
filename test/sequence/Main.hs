{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Hspec

import Lang0315.Sequence
import Lang0315.Sequences

import Control.Monad
import Control.Exception
import System.Directory
import Numeric.Natural
import Text.Printf
import Network.HTTP.Simple
import Network.HTTP.Client.Conduit (Request(checkResponse), Response (responseStatus, responseBody), HttpExceptionContent (StatusCodeException))
import Network.HTTP.Types.Status (Status(..))
import Data.Aeson
import Data.Aeson.Types (prependFailure, typeMismatch)
import qualified Data.Aeson.KeyMap as KM
import qualified Data.Vector as V

newtype R = R [Integer]

instance FromJSON R where
  parseJSON (Array vec) | not (V.null vec) =
    let res = V.head vec
    in case res of
      (Object km) -> case KM.lookup "data" km of
        Just (String t) -> pure $ R $ read $ printf "[%s]" t
        Just i -> prependFailure "cannot parse OEIS sequence, type of data: " (typeMismatch "String" i)
        Nothing -> fail "cannot parse OEIS sequence, missing data in results"
      i -> prependFailure "cannot parse OEIS sequence, contents of results: " (typeMismatch "Object" i)
  parseJSON (Array _) = fail "cannot parse OEIS sequence, empty results"
  parseJSON i = prependFailure "cannot parse OEIS sequence, " (typeMismatch "Array" i)

rootPath :: FilePath
rootPath = "cache/sequences"

makePath :: Natural -> FilePath
makePath = printf "%s/%d" rootPath

makeRequest :: Natural -> IO Request
makeRequest = fmap (\req -> req{ checkResponse = \rq rs -> do 
  let Status code _ = responseStatus rs
  guard $ code < 200 || code >= 300
  body <- responseBody rs
  let ex = StatusCodeException (void rs) body
  throwIO $ HttpExceptionRequest rq ex }) . parseRequest . printf "https://oeis.org/search?fmt=json&q=id:A%06d"

getSequence' :: Natural -> IO (Maybe [Integer])
getSequence' num = do
  let p = makePath num
  d <- try $ readFile p :: IO (Either IOException String)
  case d of
    Right str -> pure $ Just $ read str
    Left _ -> do
      oeis <- makeRequest num >>= fmap getResponseBody . httpJSON
      case oeis of
        Nothing -> pure Nothing
        Just (R seqData) -> do
          Just seqData <$ writeFile p (show seqData) -- `catch` (\(_ :: IOException) -> pure ())

main :: IO ()
main = hspec $ do
  runIO $ createDirectoryIfMissing True rootPath
  forM_ sequences $ \(num, (s, _)) -> describe (show num) $ do
    seqData <- runIO $ getSequence' num
    it "should match the OEIS" $ do
      case seqData of
        Nothing -> pendingWith $ printf "Sequence A%d could not be fetched" num
        Just s' -> take (length s') (unSequence s) `shouldBe` s'
