----------------------------------------
--  Eval.hs
--  評価器
--
--  新入生SG お手本インタプリタ
--  2012/05/23 高島尚希
----------------------------------------

module Eval where

import Control.Monad
import Control.Monad.Fix
import Syntax

-- 値
data Value
  = CONST ConstId
  | PRIM PrimId [Value]
  | LIST [Value]
  | TUPLE [Value]
  | FUN Id Expr Env
  | LEFT Value
  | RIGHT Value
  deriving Show

-- 環境
type Env = [(Id,Value)]

-- 評価
eval :: Expr -> Env -> IO Value
eval (Const id) env = return $ CONST id
eval (Prim id) env = return $ PRIM id []
eval Null env = return $ LIST []
eval (Var x) env = return v
  where (Just v) = lookup x env
eval (Fun x e) env = do
  return $ FUN x e env
eval (Let x e1 e2) env = do
  v1 <- eval e1 env
  eval e2 ((x,v1):env)
eval (LetRec x e1 e2) env = do
  v1 <- mfix $ \v -> eval e1 ((x,v):env)
  eval e2 ((x,v1):env)
eval (If e1 e2 e3) env = do
  CONST (Bool b) <- eval e1 env
  if b then eval e2 env
       else eval e3 env
eval (Force e _) env = eval e env
eval (Tuple es) env = do
  vs <- mapM (flip eval env) es
  return (TUPLE vs)
eval (Match e cases) env = do
  v <- eval e env
  evalCases cases v env
eval (App e1 e2) env = do
  v1 <- eval e1 env
  v2 <- eval e2 env
  case v1 of
    FUN x body fenv -> eval body ((x,v2):fenv)
    PRIM id arg -> evalPrim id arg v2
    v -> error ("$$$" ++ show v1 ++ "," ++ show v2 ) -- undefined

-- パターンマッチのケースを試す
evalCases :: [(Pat, Expr, Expr)] -> Value -> Env -> IO Value
evalCases [] v _ = error $ "pattern match failure: " ++ show v
evalCases ((p,g,e):cs) v env =
  case patMatch p v of
    Nothing -> evalCases cs v env
    Just env' -> do
      CONST (Bool b) <- eval g (env' ++ env)
      if b then eval e (env' ++ env)
           else evalCases cs v env

-- パターンマッチ
patMatch :: Pat -> Value -> Maybe Env
patMatch (PConst id1) (CONST id2)
  | id1 == id2 = Just []
  | otherwise = Nothing
patMatch PWild v = Just []
patMatch PNull (LIST []) = Just []
patMatch (PVar x) v = Just [(x,v)]
patMatch (PCons p1 p2) (LIST (v1:v2)) = do
  {- ここは Maybe モナド -}
  env1 <- patMatch p1 v1
  env2 <- patMatch p2 (LIST v2)
  return (env1 ++ env2)
patMatch (PTuple ps) (TUPLE vs) = do
  es <- mapM (uncurry patMatch) (zip ps vs)
  return (concat es)
patMatch (PLeft p) (LEFT v) = patMatch p v
patMatch (PRight p) (RIGHT v) = patMatch p v
patMatch _ _ = Nothing {- 失敗 -}

-- プリミティブ関数
evalPrim :: PrimId -> [Value] -> Value -> IO Value
evalPrim Neg [] (CONST (Int n)) = return $ CONST $ Int $ -n
evalPrim Not [] (CONST (Bool b)) = return $ CONST $ Bool $ not b
evalPrim FNeg [] (CONST (Double d)) = return $ CONST $ Double $ -d
evalPrim Add [CONST (Int n1)] (CONST (Int n2)) = return $ CONST $ Int $ n1 + n2
evalPrim Sub [CONST (Int n1)] (CONST (Int n2)) = return $ CONST $ Int $ n1 - n2
evalPrim Mul [CONST (Int n1)] (CONST (Int n2)) = return $ CONST $ Int $ n1 * n2
evalPrim Div [CONST (Int n1)] (CONST (Int n2)) = return $ CONST $ Int $ n1 `div` n2
evalPrim Mod [CONST (Int n1)] (CONST (Int n2)) = return $ CONST $ Int $ n1 `mod` n2
evalPrim Add [CONST (Double d1)] (CONST (Double d2)) = return $ CONST $ Double $ d1 + d2
evalPrim Sub [CONST (Double d1)] (CONST (Double d2)) = return $ CONST $ Double $ d1 - d2
evalPrim Mul [CONST (Double d1)] (CONST (Double d2)) = return $ CONST $ Double $ d1 * d2
evalPrim Div [CONST (Double d1)] (CONST (Double d2)) = return $ CONST $ Double $ d1 / d2
evalPrim Lt [v1] v2 = return $ CONST $ Bool $ evalCmpLt v1 v2
evalPrim Gt [v1] v2 = return $ CONST $ Bool $ evalCmpLt v2 v1
evalPrim Le [v1] v2 = return $ CONST $ Bool $ not $ evalCmpLt v2 v1
evalPrim Ge [v1] v2 = return $ CONST $ Bool $ not $ evalCmpLt v1 v2
evalPrim Eq [v1] v2 = return $ CONST $ Bool $ not $ evalCmpLt v1 v2 || evalCmpLt v2 v1
evalPrim Ne [v1] v2 = return $ CONST $ Bool $ evalCmpLt v1 v2 || evalCmpLt v2 v1
evalPrim And [CONST (Bool b1)] (CONST (Bool b2)) = return $ CONST $ Bool $ b1 && b2
evalPrim Or [CONST (Bool b1)] (CONST (Bool b2)) = return $ CONST $ Bool $ b1 || b2
evalPrim Cons [v] (LIST vs) = return $ LIST $ v:vs
evalPrim Append [LIST vs1] (LIST vs2) = return $ LIST $ vs1 ++ vs2
evalPrim MakeLeft [] v = return $ LEFT v
evalPrim MakeRight [] v = return $ RIGHT v
evalPrim Print [] v = evalPrint v >> return (CONST Unit)
evalPrim Chr [] (CONST (Int n)) = return $ CONST $ Char $ toEnum n
evalPrim Ord [] (CONST (Char c)) = return $ CONST $ Int $ fromEnum c
evalPrim ToInt [] (CONST (Double d)) = return $ CONST $ Int $ fromEnum d
evalPrim ToDouble [] (CONST (Int n)) = return $ CONST $ Double $ toEnum n
evalPrim id vs v = return $ PRIM id (vs++[v])

-- 値の比較
evalCmpLt :: Value -> Value -> Bool
evalCmpLt (CONST (Int n1)) (CONST (Int n2)) = n1 < n2
evalCmpLt (CONST (Bool b1)) (CONST (Bool b2)) = b1 < b2
evalCmpLt (CONST (Char c1)) (CONST (Char c2)) = c1 < c2
evalCmpLt (CONST (Double d1)) (CONST (Double d2)) = d1 < d2
evalCmpLt (CONST Unit) (CONST Unit) = False
evalCmpLt (PRIM _ _) (PRIM _ _) = error "compare closures"
evalCmpLt (LIST vs1) (LIST vs2) = and (map (uncurry evalCmpLt) (zip vs1 vs2))
evalCmpLt (TUPLE vs1) (TUPLE vs2) = and (map (uncurry evalCmpLt) (zip vs1 vs2))
evalCmpLt (FUN _ _ _) (FUN _ _ _) = error "compare closures"
evalCmpLt (LEFT v1) (LEFT v2) = evalCmpLt v1 v2
evalCmpLt (RIGHT v1) (RIGHT v2) = evalCmpLt v1 v2
evalCmpLt _ _ = undefined

-- 値の表示
evalPrint :: Value -> IO ()
evalPrint (CONST (Int n)) = putStr (show n)
evalPrint (CONST (Bool True)) = putStr "True"
evalPrint (CONST (Bool False)) = putStr "False"
evalPrint (CONST (Char c)) = putStr (c:"")
evalPrint (CONST (Double d)) = putStr (show d)
evalPrint (CONST Unit) = putStr "()"
evalPrint (PRIM _ _) = putStr "<closure>"
evalPrint (FUN _ _ _) = putStr "<closure>"
evalPrint (LIST []) = putStr "[]"
evalPrint (LIST lis@(CONST (Char c):rest)) = putStr $ map getChar lis
  where
    getChar (CONST (Char c)) = c
    getChar _ = undefined
evalPrint (LIST (v:vs)) = do
  putStr "["
  evalPrint v
  mapM (\v -> putStr ", " >> evalPrint v) vs
  putStr "]"
evalPrint (TUPLE []) = putStr "()"
evalPrint (TUPLE (v:vs)) = do
  putStr "("
  evalPrint v
  mapM (\v -> putStr ", " >> evalPrint v) vs
  putStr ")"
evalPrint (LEFT v) = putStr "(Left " >> evalPrint v >> putStr ")"
evalPrint (RIGHT v) = putStr "(Right " >> evalPrint v >> putStr ")"

-- 初期環境
initEnv :: Env
initEnv = [ ("not", PRIM Not []),
            ("Left", PRIM MakeLeft []),
            ("Right", PRIM MakeRight []),
            ("print", PRIM Print []),
            ("ord", PRIM Ord []),
            ("chr", PRIM Chr []),
            ("toInt", PRIM ToInt []),
            ("toDouble", PRIM ToDouble []) ]

-- トップレベル式を評価する
evalTop :: Id -> Expr -> Env -> IO Env
evalTop x e env = do
  v <- mfix $ \v -> eval e ((x,v):env)
  return ((x,v):env)
