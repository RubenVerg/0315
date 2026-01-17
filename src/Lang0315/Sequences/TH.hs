module Lang0315.Sequences.TH
( sequencesExpr
) where

import Language.Haskell.TH
import Numeric.Natural
import Control.Monad
import Data.Char (isDigit)
import Data.Bifunctor

import Data.FileEmbed (makeRelativeToProject)

sequenceSource :: Q String
sequenceSource = makeRelativeToProject "src/Lang0315/Sequences/Implementation.hs" >>= runIO . readFile

extractSequences :: String -> [(Natural, Name)]
extractSequences source = do
  line <- lines source
  guard $ not $ null line
  guard $ line !! (1 - 1) == 'a'
  guard $ all isDigit $ take 6 $ drop 1 line
  guard $ drop 7 line == " :: Sequence"
  let name = take 7 line
  pure (read $ drop 1 name, mkName name)

extractDescriptions :: String -> [(Natural, String)]
extractDescriptions source = do
  line <- lines source
  guard $ take 3 line == "-- "
  let text = reverse $ dropWhile (== ' ') $ reverse $ dropWhile (== ' ') $ drop 3 line
  let (bef, aft) = second (dropWhile (== ' ') . drop 1) $ span (/= ':') text
  guard $ length bef == 8
  guard $ take 2 bef == "|A"
  guard $ all isDigit $ drop 2 bef
  pure (read $ drop 2 bef, aft)

sequences :: Q [(Natural, Name, Maybe String)]
sequences = do
  source <- sequenceSource
  let seqs = extractSequences source
  let descriptions = extractDescriptions source
  pure $ flip map seqs $ \(num, ident) -> (num, ident, lookup num descriptions)

sequencesExpr :: Q Exp
sequencesExpr = ListE . map (\(num, ident, desc) -> TupE
  [ Just $ LitE $ IntegerL $ toInteger num
  , Just $ TupE [Just $ VarE ident, Just $ maybe (ConE $ mkName "Nothing") (AppE (ConE $ mkName "Just") . LitE . StringL) desc ]]) <$> sequences
