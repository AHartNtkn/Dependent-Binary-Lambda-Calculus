module DBLC where

import qualified Data.Map.Strict as Map
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans.Except

import System.IO
import System.Environment

-- The proof environment monad.
-- Contains a map from de bruijn levels to terms
-- a context containing the types for de bruijn indices,
-- and an integer representing the level.
type Proof = ExceptT String (ReaderT [Term] (StateT (Map.Map Int (Term, Term)) (State Int)))

runProof p = fst $ evalState (runStateT (runReaderT (runExceptT p) []) Map.empty) 0

-- Basic abstract syntax
infixl 9 :%
data Term
    = Lam Term Term
    | Var Int
    | Level Int
    | Term :% Term
    | U
    deriving (Eq, Show)

-- ======= Evaluation =======

-- Check if a variable occures freely in a term
freeIn (Var x)    n = x == n
freeIn (d :% d1)  n = freeIn d n || freeIn d1 n
freeIn (Lam t tp) n = freeIn t n || freeIn tp (1 + n)
freeIn _          n = False

-- Increment free variables
quote n (Var x)   = if x >= n then Var (1 + x) else Var x
quote n (Lam t d) = Lam (quote n t) (quote (1 + n) d)
quote n (d :% b)  = quote n d :% quote n b
quote n x         = x

sub s n (Var x) =
  case x `compare` n of
    GT -> Var (x - 1)
    EQ -> s
    LT -> Var x
sub s n (Lam t d) = Lam (sub s n t) (sub (quote 0 s) (1 + n) d)
sub s n (d :% b)  = sub s n d :% sub s n b
sub s n x         = x

-- Reduce a term to weak head normal form.
whnf' :: Bool -> Term -> Proof Term
whnf' names ee = spine ee [] where
  spine :: Term -> [Term] -> Proof Term
  spine (f :% a) as = spine f (a:as)
  spine (Lam t z) (u:as) = spine (sub u 0 z) as
  -- Eta conversion
  spine (Lam t (tp :% Var 0)) [] =
            if freeIn tp 0
            then return (Lam t (tp :% Var 0))
            else spine (sub (Var 0) 0 tp) []
  spine (Level i) as = 
    if names -- Should names/levels be removed
    then do
      tbl <- get
      case Map.lookup i tbl of
        Nothing -> throwError $ "Level " ++ show i ++ " not found in context (whnf)."
        Just t  -> spine (fst t) as
    else app (Level i) as
  spine f as = app f as
  app f as = return $ foldl (:%) f as

whnf = whnf' False
nwhnf = whnf' True

-- Normal Form
nf' :: Term -> Proof Term
nf' ee = spine ee [] where
  spine (f :% a) as = spine f (a:as)
  -- Eta conversion
  spine (Lam t (tp :% Var 0)) [] =
            if freeIn tp 0
            then Lam <$> nf' t <*> nf' (tp :% Var 0)
            else spine (sub (Var 0) 0 tp) []
  spine (Lam t e) [] = Lam <$> nf' t <*> nf' e
  spine (Lam t e) (u:as) = spine (sub u 0 e) as
  spine (Level i) as = do
        tbl <- get
        case Map.lookup i tbl of
          Nothing -> throwError $ "Level " ++ show i ++ " not found in context."
          Just t  -> spine (fst t) as
  spine f as = foldl (:%) f <$> mapM nf' as

nf d = do
  r <- nf' d
  if d == r
  then return r
  else nf r

-- ======= Type Checking =======

infer :: Term -> Proof Term
infer t = do
  wt <- whnf t
  case wt of
    Level i -> do
      tbl <- get
      case Map.lookup i tbl of
           Nothing -> throwError $ "Level " ++ show i ++ " not found in context durring type inference."
           Just t  -> return $ snd t
    Var n -> do
      ctx <- ask
      case (ctx , n) of
        ([], _) -> throwError $ "Cannot infer term variable in empty context."
        (x:g, 0) -> local tail $ do
                       check x U
                       return (quote 0 x)
        (_:g, n) -> local tail $ do
                       ty <- infer (Var (n - 1))
                       return (quote 0 ty)
    tr1 :% tr2 -> do
      ty1' <- infer tr1
      ty1  <- nwhnf ty1'
      case ty1 of
        Lam tp1 tp2 -> do
          check tr2 tp1
          return (sub tr2 0 tp2)
    Lam ty1 ty2 -> do
      check ty1 U
      local (ty1:) $ do
        check ty2 U
        return U
    U -> return U

check :: Term -> Term -> Proof ()
check tr ty =
  case tr of
    Level i -> do
      tbl <- get
      case Map.lookup i tbl of
           Nothing -> throwError $ "Level " ++ show i ++ " not found in context durring type checking."
           Just (_, t)  -> do
             tnf  <- nf t
             tynf <- nf ty
             if tnf == tynf
             then return ()
             else throwError $ "Type didn't match durring lookup."
    Var n -> do
      ctx <- ask
      case (ctx , n) of
        ([], _) -> throwError $ "Cannot check type of variable term in an empty context."
        (x:g, 0) -> do
          xnf  <- nf (quote 0 x)
          tynf <- nf ty
          if tynf == xnf
          then do 
            check ty U 
            local tail $ check x U
          else throwError $ "Term does not have correct type."
        (_:g, _) -> local tail $ check (Var (n - 1)) (sub (Var 0) 0 ty)
    Lam aty tr' -> do
      ctx <- get
      tyw <- nwhnf ty
      case tyw of
        Lam ty1 ty2 -> do
          ty1nf <- nf ty1
          atynf <- nf aty
          if ty1nf == atynf
          then local (ty1:) $ check tr' ty2
          else throwError $ "Type of lam annotation didn't match type annotation."
        U -> do
          check aty U
          local (aty:) $ check tr' U
        _ -> throwError $ "Lambdas can only be Lam or * types."
    tr1 :% tr2 -> do
      ity <- infer (tr1 :% tr2)
      tynf <- nf ty
      itynf <- nf ity
      if tynf == itynf
      then check ty U
      else throwError $ "Failed to unify at application."
    U -> do
      tyw <- nwhnf ty
      case tyw of
        U -> return ()
        _ -> throwError $  "* can only have type *."

-- ======= Concrete Syntax =======

-- Parse a string of 1s and 0s into a collection of terms
data Token
  = PLam 
  | PVar Int
  | PLevel Int
  | PApp
  | PU

parse :: String -> [Token] -> [Term] -> [Term]
-- Tokenize
parse e@('1':_)       p  [] = let (i, s) = readInt e in parse s (PVar (i-1):p) []
parse ('0':'0':s)     p  [] = parse s (PApp:p) []
parse ('0':'1':'0':s) p  [] = parse s (PLam:p) []
parse ('0':'1':'1':s) p  [] = case readInt s of
  (0, s') -> parse s' (PU:p)           []
  (i, s') -> parse s' (PLevel (i-1):p) []
-- Build ASTs
parse [] (PLam:p)     (a:b:stk) = parse [] p (Lam a b:stk)
parse [] (PU:p)       stk       = parse [] p (U:stk)
parse [] (PApp:p)     (a:b:stk) = parse [] p ((a :% b):stk)
parse [] (PVar i:p)   stk       = parse [] p (Var i:stk)
parse [] (PLevel i:p) stk       = parse [] p (Level i:stk)
-- Finish
parse [] [] t = t

readInt :: String -> (Int, String)
readInt ('1':s) = let (i, s') = readInt s in (i+1, s')
readInt ('0':s) = (0,s)

toBin :: Term -> String
toBin (Lam a b) = "010" ++ toBin a ++ toBin b
toBin (a :% b) = "00" ++ toBin a ++ toBin b
toBin (Var i) = numToBin i
toBin (Level i) = "011" ++ numToBin i
toBin U = "0110"

numToBin :: Int -> String
numToBin 0 = "10"
numToBin i = '1' : numToBin (i-1)

output :: Proof a -> String 
output p = case runState (runStateT (runReaderT (runExceptT p) []) Map.empty) 0 of
    ((_, mp'), lvl) -> case toBin <$> fst <$> Map.lookup (lvl-1) mp' of
                         Just s -> s
                         Nothing -> ""

checkProg :: String -> Proof ()
checkProg s = go (parse s [] []) where
  go :: [Term] -> Proof ()
  go (ty:tr:ctx) = do
    check tr ty
    lvl <- lift $ lift $ lift $ get
    tbl <- get
    modify $ Map.insert lvl (tr, ty)
    lift $ lift $ lift $ modify (+1)
    go ctx
  go (_:[]) = throwError $ "Type is given without implementation."
  go [] = return ()

-- ======= Input / Output =======

extention = ".dblc"

endQ :: String -> Bool
endQ s = extention == reverse (take (length extention) (reverse s))

proveFile :: String -> IO ()
proveFile f | endQ f = do
               fileContents <- readFile f
               let res = checkProg fileContents
               case runProof res of
                 Right () -> do putStrLn "Checking Successful!"
                                putStrLn $ output res
                 Left e   -> putStrLn e
            | otherwise = proveFile (f ++ extention)

-- Main program
main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  args <- getArgs
  case args of
   name:_ -> proveFile name
   _      -> putStrLn "No file provided."


