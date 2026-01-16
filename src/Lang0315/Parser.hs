module Lang0315.Parser
( Expr(..)
, parse
, parseMany
) where

import Prelude hiding (sequence)

import Text.Megaparsec hiding (parse)
import qualified Text.Megaparsec as P
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr

import Numeric.Natural
import Data.Void
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Bifunctor (first)
import Data.Function ((&))

data Expr
  = ExprSequence Natural
  | ExprNegate Expr
  | ExprAbs Expr
  | ExprAdd Expr Expr
  | ExprSubtract Expr Expr
  | ExprMultiply Expr Expr
  | ExprDivide Expr Expr
  | ExprModulo Expr Expr
  | ExprPower Expr Expr
  | ExprEqual Expr Expr
  | ExprLess Expr Expr
  | ExprComma Expr Expr
  | ExprSemi Expr Expr
  | ExprCharacter Expr
  | ExprCut Expr
  | ExprJoin Expr Expr
  | ExprIndex Expr Expr
  | ExprKeep Expr Expr
  | ExprName String
  | ExprAssign String Expr
  | ExprEmpty
  deriving (Show, Eq)

type Parser = Parsec Void String

spaceConsumer :: Parser ()
spaceConsumer = L.space hspace1 (L.skipLineComment "//") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

sequence :: Parser Expr
sequence = lexeme $ ExprSequence . read <$> some digitChar

nameOrAssign :: Parser Expr
nameOrAssign = do
  name <- lexeme $ some letterChar
  option (ExprName name) $ do
    _ <- lexeme $ char ':'
    ExprAssign name <$> expr

subscriptable :: Parser Expr
subscriptable = sequence <|> nameOrAssign <|> between (lexeme $ char '(') (lexeme $ char ')') expr

subscript :: Char -> Char -> (Expr -> Expr -> Expr) -> Parser (Expr -> Expr)
subscript l r f = flip f <$> between (lexeme $ char l) (lexeme $ char r) expr

subscripted :: Parser Expr -> Parser (Expr -> Expr) -> Parser Expr
subscripted a s = foldl (&) <$> a <*> many s

term :: Parser Expr
term = subscripted subscriptable (subscript '[' ']' ExprIndex <|> subscript '{' '}' ExprKeep)

expr :: Parser Expr
expr = lexeme $ makeExprParser term
  [ [ ms [ op '-' ExprNegate, op '|' ExprAbs, op '&' ExprCharacter ] ]
  , [ InfixL $ op '.' ExprIndex ]
  , [ InfixR $ op '^' ExprPower ]
  , [ InfixL $ op '*' ExprMultiply, InfixL $ op '/' ExprDivide, InfixL $ op '%' ExprModulo ]
  , [ InfixL $ op '+' ExprAdd, InfixL $ op '-' ExprSubtract ]
  , [ InfixR $ op '~' ExprJoin ]
  , [ InfixN $ op '<' ExprLess ]
  , [ InfixN $ op '=' ExprEqual ]
  , [ InfixN $ op ',' ExprComma, InfixN $ op ';' ExprSemi ]
  , [ ms [ op '_' ExprCut ] ]
  ]
  where
    op c e = lexeme $ char c $> e
    ms cs = Prefix $ foldr1 (.) <$> some (choice cs)

prettyError :: String -> SourcePos -> String
prettyError source pos = let
  ls = lines source
  line = subtract 1 $ unPos $ sourceLine pos
  column = subtract 1 $ unPos $ sourceColumn pos
  theLine = if length ls <= line then "" else ls !! line
  in sourceName pos ++ ":" ++ show (unPos $ sourceLine pos) ++ ":" ++ show (unPos $ sourceColumn pos) ++ "\n" ++ theLine ++ "\n" ++ replicate column ' ' ++ "^\n"

prettyParseError :: String -> SourcePos -> ParseError String Void -> String
prettyParseError source pos err = prettyError source pos ++ parseErrorTextPretty err

makeParseErrors :: String -> ParseErrorBundle String Void -> String
makeParseErrors source es = case attachSourcePos errorOffset (bundleErrors es) (bundlePosState es) of
  (r :| rs, _) -> concatMap (uncurry $ flip (prettyParseError source)) $ r : rs

makeParser :: Parser a -> FilePath -> String -> Either String a
makeParser p file source = first (makeParseErrors source) $ P.parse (spaceConsumer *> p <* eof) file source

parse :: FilePath -> String -> Either String Expr
parse = makeParser expr

parseMany :: FilePath -> String -> Either String [Expr]
parseMany = makeParser (sepEndBy (expr <|> lexeme (pure ExprEmpty)) (some newline))
