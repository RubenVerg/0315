module Lang0315.Interpreter
( interpret
, Context
, runContext
) where

import Lang0315.Parser (Expr(..))
import Lang0315.Sequence
import Lang0315.Sequences

import Control.Monad.State
import Control.Monad.Except

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
