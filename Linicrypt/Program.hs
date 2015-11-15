module Linicrypt.Program where

--------------------------------------------------------------------------------
-- todo

-- find recoverable nodes given some subset of refs
--   -linicrypt

--------------------------------------------------------------------------------
-- imports

import qualified Data.Bimap as B
import Control.Monad.State
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- types

type Ref  = Int

data Expr = Xor Ref Ref
          | Not Ref
          | G Ref
          | Input Int
          deriving (Eq, Ord, Show)

type Prog = B.Bimap Ref Expr

type P = State Prog

--------------------------------------------------------------------------------
-- fancy stuff

recoverable :: [Ref] -> Prog -> [Ref]
recoverable known prog = evalState runIt prog
  where
    runIt = do
      refs <- topoSort
      recover (S.fromList known) (concat (replicate (length refs) refs))

    recover known [] = return (S.toList known)
    recover known (ref:refs) = do
        expr <- ref2Expr ref

        case expr of
          (Xor x y) ->
            if S.member x known && S.member y known then
              recover (S.insert ref known) refs
            else if S.member y known && S.member ref known then
              recover (S.insert x known) refs
            else if S.member x known && S.member ref known then
              recover (S.insert y known) refs
            else
              recover known refs

          (Not x) ->
            if S.member x known then
              recover (S.insert ref known) refs
            else if elem ref known then
              recover (S.insert x known) refs
            else
              recover known refs

          (G x) ->
            if S.member x known then
              recover (S.insert ref known) refs
            else
              recover known refs

          (Input _) -> recover known refs


newProg :: P a -> Prog
newProg m = execState m B.empty

showProg :: Prog -> String
showProg prog = unlines $ evalState (evalStateT doit B.empty) prog
  where
    doit :: StateT (B.Bimap Ref Char) P [String]
    doit = do
      refs <- lift topoSort
      mapM showLine refs

    showLine :: Ref -> StateT (B.Bimap Ref Char) P String
    showLine ref = do
      expr <- lift (ref2Expr ref)
      a    <- getName ref
      case expr of
        (Xor x y) -> do
          b <- getName x
          c <- getName y
          return $ concat [a, " = Xor (", b, ", ", c, ")"]
        (Not x) -> do
          b <- getName x
          return $ concat [a, " = not(", b, ")"]
        (G x) -> do
          b <- getName x
          return $ concat [a, " = G(", b, ")"]
        (Input n) -> do
          return $ concat [a, " <- Input ", show n]

    getName :: Ref -> StateT (B.Bimap Ref Char) P String
    getName ref = do
      m <- get
      if ref `B.member` m then
        return [m B.! ref]
      else do
        let sym = if B.size m == 0 then 'a' else succ $ maximum $ B.elems m
        put (B.insert ref sym m)
        return [sym]

topoSort :: P [Ref]
topoSort = do
    refs <- gets B.keys
    reverse <$> fold refs []
  where
    recurse :: Ref -> [Ref] -> P [Ref]
    recurse ref seen =
      if ref `elem` seen then
        return seen
      else do
        expr <- ref2Expr ref
        fold (getArgs expr) seen
        return (ref : seen)

    fold :: [Ref] -> [Ref] -> P [Ref]
    fold []     seen = return seen
    fold (x:xs) seen = do
      seen' <- recurse x seen
      fold xs seen'

getArgs :: Expr -> [Ref]
getArgs (Xor x y) = [x, y]
getArgs (Not x)   = [x]
getArgs (G x)     = [x]
getArgs (Input _) = []

--------------------------------------------------------------------------------
-- helpers

insert :: Ref -> Expr -> P ()
insert ref expr = do
  b <- get
  put $ B.insert ref expr b

freshRef :: P Ref
freshRef = do
  b <- get
  if B.size b > 0 then
    return $ succ $ maximum $ B.keys b
  else
    return 0

ref2Expr :: Ref -> P Expr
ref2Expr ref = do
  b <- get
  if (B.member ref b) then
    return (b B.! ref)
  else
    error "[ref2Expr] no ref"

expr2Ref :: Expr -> P Ref
expr2Ref expr = do
  b <- get
  if (B.memberR expr b) then
    return (b B.!> expr)
  else
    error "[expr2Ref] no expr"

insertExpr :: Expr -> P Ref
insertExpr expr = do
  b <- get
  if (B.memberR expr b) then
    return (b B.!> expr)
  else do
    ref <- freshRef
    insert ref expr
    return ref

--------------------------------------------------------------------------------
-- program dsl

inp :: Int -> P Ref
inp n = insertExpr (Input n)

xor :: Ref -> Ref -> P Ref
xor x y = insertExpr (Xor x y)

not :: Ref -> P Ref
not x = insertExpr (Not x)

g :: Ref -> P Ref
g x = insertExpr (G x)

--------------------------------------------------------------------------------
-- test

p1 = newProg $ do
  a <- inp 0
  b <- inp 1
  _ <- xor a b
  _ <- g a
  g b
