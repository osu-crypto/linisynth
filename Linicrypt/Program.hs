module Linicrypt.Program where

--------------------------------------------------------------------------------
-- imports

import Prelude hiding (not)

import qualified Data.Bimap as B
import Control.Monad.State
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- types

type Ref  = Int

data Expr = Xor Ref Ref
          | Not Ref
          | RandOracle Ref
          | Rand Int                  -- need an id to distingish invocations
          deriving (Eq, Ord, Show)

data Prog = Prog { p_refMap  :: B.Bimap Ref Expr
                 , p_outputs :: [Ref]
                 }

type P = State Prog

{-instance Monoid Prog where-}
  {-mempty = Prog { p_refMap = B.empty, p_outputs = [] }-}
  {-mappend a b = undefined-}
  {--- need to freshen references of prog b-}

type Vector = [Int]
type Matrix = [Vector]

data Linicrypt = Linicrypt { l_constraints :: [(Vector, Vector)]
                           , l_matrix      :: Matrix
                           , l_oracles     :: [Ref]
                           , l_out         :: Vector
                           } deriving (Show)

--------------------------------------------------------------------------------
-- convert linicrypt

-- TODO: Refs can't be used to index into the matrix

type L = StateT Linicrypt P

trevnoc :: Linicrypt -> Prog
trevnoc = undefined

convert :: Prog -> Linicrypt
convert prog = evalState (execStateT doit emptyLinicrypt) prog
  where
    emptyLinicrypt = Linicrypt [] [] [] []

    refs = B.keys (p_refMap prog)
    doit = do
      mapM oracle     refs
      mapM matrix     refs
      mapM constraint refs

oracle :: Ref -> L ()
oracle ref = do
    expr <- lift (ref2Expr ref)
    case expr of
      Rand _       -> addOracle ref
      RandOracle _ -> addOracle ref
      _            -> return ()

matrix :: Ref -> L ()
matrix ref = do
    expr <- lift (ref2Expr ref)
    n    <- getSize
    case expr of
      Xor x y      -> addRow ref [ if i == y || i == x then 1 else 0 | i <- [ 0 .. n ] ]
      Not x        -> addRow ref [ if i == x then -1 else 0          | i <- [ 0 .. n ] ]
      RandOracle x -> addRow ref [ if i == x then 1 else 0           | i <- [ 0 .. n ] ]
      _            -> return ()

constraint :: Ref -> L ()
constraint ref = do
    expr <- lift (ref2Expr ref)
    case expr of
      RandOracle x -> do
        before <- getRow x
        after  <- getRow ref
        addConstraint (before, after)
      _ -> return ()

addOracle :: Ref -> L ()
addOracle ref = modify $ \l -> l { l_oracles = l_oracles l ++ [ref] }

addConstraint :: (Vector, Vector) -> L ()
addConstraint pair = modify $ \l -> l { l_constraints = l_constraints l ++ [pair] }

addRow :: Ref -> Vector -> L ()
addRow ref vec = modify $ \l -> l { l_matrix = insertAt ref vec (l_matrix l) }

getSize :: L Int
getSize = gets (length . l_oracles)

getRow :: Ref -> L Vector
getRow ref = do
    m <- gets l_matrix
    return (m `at` ref)

at :: Matrix -> Ref -> Vector
at m ref = m !! ref

-- TODO: make this more robust
insertAt :: Int -> a -> [a] -> [a]
insertAt ix val xs = take ix xs ++ [val] ++ drop (ix+1) xs

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

          (RandOracle x) ->
            if S.member x known then
              recover (S.insert ref known) refs
            else
              recover known refs

          (Rand _) -> recover known refs


emptyProg :: Prog
emptyProg = Prog { p_refMap = B.empty, p_outputs = [] }

newProg :: P a -> Prog
newProg m = execState m emptyProg

printProg :: Prog -> IO ()
printProg p = putStr (showProg p)

showProg :: Prog -> String
showProg prog = evalState doit prog
  where
    doit :: P String
    doit = do
      refs  <- topoSort
      lines <- unlines <$> mapM showLine refs
      let output = "output (" ++ concat (map show (p_outputs prog)) ++ ")\n"
      return (lines ++ output)

    showLine :: Ref -> P String
    showLine ref = do
      expr <- ref2Expr ref
      case expr of
        (Xor x y) -> do
          return $ concat [show ref, " = Xor (", show x, ", ", show y, ")"]
        (Not x) -> do
          return $ concat [show ref, " = not(", show x, ")"]
        (RandOracle x) -> do
          return $ concat [show ref, " = RO(", show x, ")"]
        (Rand n) -> do
          return $ concat [show ref, " <- $"]

topoSort :: P [Ref]
topoSort = do
    refs <- gets (B.keys . p_refMap)
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
getArgs (Xor x y)      = [x, y]
getArgs (Not x)        = [x]
getArgs (RandOracle x) = [x]
getArgs (Rand _)       = []

--------------------------------------------------------------------------------
-- helpers

insert :: Ref -> Expr -> P ()
insert ref expr = do
  b <- gets p_refMap
  let b' = B.insert ref expr b
  modify $ \p -> p { p_refMap = b' }

freshRef :: P Ref
freshRef = do
  b <- gets p_refMap
  if B.size b > 0 then
    return $ succ $ maximum $ B.keys b
  else
    return 0

ref2Expr :: Ref -> P Expr
ref2Expr ref = do
  b <- gets p_refMap
  if (B.member ref b) then
    return (b B.! ref)
  else
    error "[ref2Expr] no ref"

expr2Ref :: Expr -> P Ref
expr2Ref expr = do
  b <- gets p_refMap
  if (B.memberR expr b) then
    return (b B.!> expr)
  else
    error "[expr2Ref] no expr"

insertExpr :: Expr -> P Ref
insertExpr expr = do
  b <- gets p_refMap
  if (B.memberR expr b) then
    return (b B.!> expr)
  else do
    ref <- freshRef
    insert ref expr
    return ref

--------------------------------------------------------------------------------
-- program dsl

rand :: Int -> P Ref
rand n = insertExpr (Rand n)

xor :: Ref -> Ref -> P Ref
xor x y = insertExpr (Xor x y)

not :: Ref -> P Ref
not x = insertExpr (Not x)

ro :: Ref -> P Ref
ro x = insertExpr (RandOracle x)

output :: [Ref] -> P ()
output refs = modify $ \p -> p { p_outputs = p_outputs p ++ refs }

--------------------------------------------------------------------------------
-- test

p1 = newProg $ do
  a <- rand 0
  b <- rand 1
  c <- not b
  d <- ro c
  e <- xor a d
  output [e]
