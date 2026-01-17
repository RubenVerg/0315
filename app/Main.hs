module Main (main) where

import Lang0315.Parser
import Lang0315.Interpreter
import Lang0315.Sequence
import Lang0315.Sequences

import System.IO
import Control.Monad
import System.Exit
import qualified Options.Applicative as Opts

data Options
  = ReplOptions { displayLength :: Int }
  | FileOptions { maxLength :: Maybe Int, nth :: Maybe Int, filePath :: FilePath }
  | CountOptions

options :: Opts.Parser Options
options =
  (ReplOptions
    <$> Opts.option Opts.auto
      (  Opts.long "repl-length"
      <> Opts.short 'L'
      <> Opts.help "Maximum display length of sequences in REPL"
      <> Opts.metavar "LENGTH"
      <> Opts.value 25
      )
  ) Opts.<|> (FileOptions
    <$> Opts.option (Just <$> Opts.auto)
      (  Opts.long "max-length"
      <> Opts.short 'l'
      <> Opts.help "Cut the final sequence to a maximum length"
      <> Opts.metavar "LENGTH"
      <> Opts.value Nothing
      )
    <*> Opts.option (Just <$> Opts.auto)
      (  Opts.long "index"
      <> Opts.short 'n'
      <> Opts.help "Only display an index in the final sequence"
      <> Opts.metavar "INDEX"
      <> Opts.value Nothing)
    <*> Opts.argument Opts.str (Opts.metavar "PATH")
  ) Opts.<|> Opts.flag' CountOptions
      (  Opts.long "count-sequences"
      <> Opts.short 'C'
      <> Opts.help "Display the amount of sequences available")

disp :: Maybe Int -> Int -> Sequence -> IO ()
disp (Just l) c _ | c >= l = putStrLn ""
disp _ _ (Sequence []) = putStrLn ""
disp l c (Sequence (x:xs)) = do
  putStr $ show x ++ " "
  hFlush stdout
  disp l (c + 1) $ Sequence xs

main :: IO ()
main = do
  -- disp (Just 10) 0 $ Sequence $ flip map [2, 4..] $ flip adicValuation 2
  opts <- Opts.execParser $ Opts.info (Opts.helper <*> options) Opts.fullDesc
  case opts of
    ReplOptions{ displayLength = len } -> repl len []
    FileOptions{ maxLength = len, nth = nth, filePath = path } -> runFile len nth path
    CountOptions -> print $ length sequences

runFile :: Maybe Int -> Maybe Int -> FilePath -> IO ()
runFile l nth path = do
  f <- readFile path
  let (_, result) = runCode [] path f
  case result of
    Left err -> putStrLn err *> exitFailure
    Right s -> case nth of
      Just n -> print $ unSequence s !! n
      Nothing -> disp l 0 s

repl :: Int -> [(String, Sequence)] -> IO ()
repl l ctx = do
  putStr "> "
  hFlush stdout
  i <- getLine
  when (i /= "") $ do
    let (ctx', result) = runCode ctx "<repl>" i
    case result of
      Left err -> putStrLn err
      Right res -> disp (Just l) 0 res
    repl l ctx'

runCode :: [(String, Sequence)] -> FilePath -> String -> ([(String, Sequence)], Either String Sequence)
runCode ctx path code = case parseMany path code of
  Left err -> (ctx, Left err)
  Right expr -> case runContext ctx $ mapM interpret expr of
    (Left err, ctx') -> (ctx', Left err)
    (Right [], ctx') -> (ctx', Left "Empty file!")
    (Right ss, ctx') -> (ctx', Right $ last ss)
