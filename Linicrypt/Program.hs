module Linicrypt.Program where

--------------------------------------------------------------------------------
-- imports

import Control.Monad.State
import Data.Maybe (fromMaybe)
import Data.List (intercalate)
import qualified Data.Set   as S
import qualified Data.Bimap as B
import qualified Data.Map   as M

--------------------------------------------------------------------------------
-- types

-- field elements are from Z_p
const_p    = 2
const_zero = 0

type Ref  = Int

data Expr = Plus [Ref]
          | RandOracle [Ref]
          | Rand Int                  -- need an id to distingish invocations
          deriving (Eq, Ord, Show)

data Prog = Prog { p_refMap  :: B.Bimap Ref Expr
                 , p_outputs :: [Ref]
                 }

type P = State Prog

type Vector = [Int]
type Matrix = [Vector]

data Linicrypt = Linicrypt { l_constraints :: [(Matrix, Vector)]
                           , l_matrix      :: Matrix
                           , l_out         :: Matrix
                           } deriving (Show)

--------------------------------------------------------------------------------
-- convert linicrypt

data LState = LState { lstate_ctr  :: Int
                     , lstate_size :: Int
                     , lstate_row  :: M.Map Ref Int
                     , lstate_l    :: Linicrypt
                     }

type L = StateT LState P

trevnoc :: Linicrypt -> Prog
trevnoc = undefined

convert :: Prog -> Linicrypt
convert prog = lstate_l $ evalState (execStateT doit emptyLState) prog
  where

    emptyLState :: LState
    emptyLState = LState 0 0 M.empty (Linicrypt [] [] [])

    refs = B.keys (p_refMap prog)

    doit :: L ()
    doit = do
      mapM_ countFreshVars refs
      n <- gets lstate_ctr
      modify $ \ls -> ls { lstate_size = n }
      setCtr 0
      mapM_ genMatrix refs
      mapM_ constraint refs
      mapM_ copyOutput (p_outputs prog)

countFreshVars :: Ref -> L ()
countFreshVars ref = do
    expr <- lift (ref2Expr ref)
    case expr of
      Rand _       -> bumpCtr >> return ()
      RandOracle _ -> bumpCtr >> return ()
      _            -> return ()

genMatrix :: Ref -> L ()
genMatrix ref = do
    expr <- lift (ref2Expr ref)
    n    <- gets lstate_size

    case expr of
      Plus xs -> do
        rs <- mapM ref2Row xs
        let zero = replicate n const_zero
        putRow ref (foldr addRows zero rs)

      RandOracle x -> do
        c <- bumpCtr
        putRow ref [ if i == c then 1 else 0 | i <- [ 0 .. n-1 ] ]

      Rand _ -> do
        c <- bumpCtr
        putRow ref [ if i == c then 1 else 0 | i <- [ 0 .. n-1 ] ]

copyOutput :: Ref -> L ()
copyOutput ref = do
    row <- ref2Row ref
    modifyLinicrypt $ \l -> l { l_out = l_out l ++ [row] }

addRows :: Vector -> Vector -> Vector
addRows x y = zipWith (\x y -> (x + y) `mod` const_p) x y

constraint :: Ref -> L ()
constraint ref = do
    expr <- lift (ref2Expr ref)
    case expr of
      RandOracle xs -> do
        before <- mapM getRow xs
        after  <- getRow ref
        addConstraint (before, after)
      _ -> return ()

addConstraint :: (Matrix, Vector) -> L ()
addConstraint pair = modifyLinicrypt $ \l -> l { l_constraints = l_constraints l ++ [pair] }

bumpCtr :: L Int
bumpCtr = do
    n <- gets lstate_ctr
    modify $ \ls -> ls { lstate_ctr = n + 1 }
    return n

setCtr :: Int -> L ()
setCtr n = modify $ \ls -> ls { lstate_ctr = n }

ref2Row :: Ref -> L Vector
ref2Row ref = do
    rowMap <- gets lstate_row
    let rowNum = fromMaybe (error "[row] no row") (M.lookup ref rowMap)
    getRow rowNum

getRow :: Int -> L Vector
getRow i = do
    m <- gets (l_matrix . lstate_l)
    return (m !! i)

modifyLinicrypt :: (Linicrypt -> Linicrypt) -> L ()
modifyLinicrypt f = modify $ \ls -> ls { lstate_l = f (lstate_l ls)}

putRow :: Ref -> Vector -> L ()
putRow ref vec = do
    m <- gets (l_matrix . lstate_l)
    let m' = m ++ [vec]
        ix = length m
    modifyLinicrypt $ \l -> l { l_matrix = m' }
    modify $ \ls -> ls { lstate_row = M.insert ref ix ( lstate_row ls ) }

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
          (Plus xs) -> do
            let vars = S.fromList (ref : xs)
            if S.size (S.difference vars known) == 1 then do
              let recovered = S.elemAt 0 (S.difference vars known)
              recover (S.insert recovered known) refs
            else
              recover known refs

          (RandOracle xs) ->
            if all (`S.member` known) xs then
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
      let output = "output(" ++ intercalate ", " (map show (p_outputs prog)) ++ ")\n"
      return (lines ++ output)

    showLine :: Ref -> P String
    showLine ref = do
      expr <- ref2Expr ref
      case expr of
        (Plus xs) -> do
          return $ concat [show ref, " = Plus(", intercalate ", " (map show xs), ")"]
        (RandOracle xs) -> do
          return $ concat [show ref, " = H(", intercalate ", " (map show xs), ")"]
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
getArgs (Plus xs)       = xs
getArgs (RandOracle xs) = xs
getArgs (Rand _)        = []

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

plus :: [Ref] -> P Ref
plus xs = insertExpr (Plus xs)

h :: [Ref] -> P Ref
h xs = insertExpr (RandOracle xs)

output :: [Ref] -> P ()
output refs = modify $ \p -> p { p_outputs = p_outputs p ++ refs }

--------------------------------------------------------------------------------
-- test

p1 = newProg $ do
  a <- rand 0
  b <- rand 1
  c <- plus [a, b]
  d <- h [c]
  e <- plus [a, d]
  output [c, e]
