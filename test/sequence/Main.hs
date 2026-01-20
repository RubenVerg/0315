module Main (main) where

import Test.Hspec

import Lang0315.Sequence
import Lang0315.Sequences

import Control.Monad
import Control.Exception
import System.Directory
import Numeric.Natural
import Text.Printf
import qualified Data.Text as T
import qualified Math.OEIS as OEIS

rootPath :: FilePath
rootPath = "cache/sequences"

makePath :: Natural -> FilePath
makePath = printf "%s/%d" rootPath

getSequence' :: Natural -> IO (Maybe [Integer])
getSequence' num = do
  let p = makePath num
  d <- try $ readFile p :: IO (Either IOException String)
  case d of
    Right str -> pure $ Just $ read str
    Left _ -> do
      oeis <- OEIS.lookupSeq' (OEIS.ID $ T.pack $ printf "A%d" num)
      case OEIS.seqData <$> oeis of
        Nothing -> pure Nothing
        Just seqData -> do
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
