----------------------------------------
--  Syntax.hs
--  抽象構文木の定義
--
--  新入生SG お手本インタプリタ
--  2012/05/23 高島尚希
----------------------------------------

module Syntax where

import Control.Monad

--------------------------------
-- トップレベル式
--------------------------------

type TopExpr = [(Id, TypeString, Expr)]
type TypeString = String

printTopExpr :: TopExpr -> IO ()
printTopExpr = mapM_ $ \(f,t,_) -> putStrLn $ f ++ " :: " ++ t


--------------------------------
-- 式
--------------------------------

-- 識別子(変数名,関数名)
type Id = String

-- 式の抽象構文木
data Expr
  = Const ConstId
  | Prim PrimId
  | Var Id
  | Fun Id Expr
  | App Expr Expr
  | If Expr Expr Expr
  | Let Id Expr Expr
  | LetRec Id Expr Expr
  | Force Expr Type
  | Match Expr [(Pat, Expr, Expr)]
  | Tuple [Expr]
  | Null
  deriving Show

-- 定数
data ConstId
  = Int Int
  | Bool Bool
  | Char Char
  | Double Double
  | Unit
  deriving (Show,Eq)

-- プリミティブ関数
data PrimId
  = Neg | Not | FNeg
  | Add | Sub | Mul | Div | Mod
  | FAdd | FSub | FMul | FDiv
  | Lt | Le | Gt | Ge | Eq | Ne
  | And | Or
  | Cons | Append
  | MakeLeft | MakeRight | Print
  | Chr | Ord | ToInt | ToDouble
  deriving Show

-- パターン
data Pat
  = PConst ConstId
  | PWild
  | PNull
  | PVar Id
  | PCons Pat Pat
  | PTuple [Pat]
  | PLeft Pat
  | PRight Pat
  deriving Show

--------------------------------
-- 型
--------------------------------

-- 型スキーム
data TypeScheme
  = ForAll [TVar] Type
      deriving Eq

-- 型
data Type
  = TInt
  | TBool
  | TChar
  | TDouble
  | TUnit
  | TList Type
  | TFun Type Type
  | TVar TVar
  | TVarName String
  | TTuple [Type]
  | TEither Type Type
  deriving Eq

-- 型変数
type TVar = Int


--------------------------------
-- 型の表示
--------------------------------

-- Show クラスのインスタンスにする
instance Show Type where
  show TInt = "Int"
  show TBool = "Bool"
  show TChar = "Char"
  show TDouble = "Double"
  show TUnit = "()"
  show (TList TChar) = "String"
  show (TList t) = "[" ++ show t ++ "]"
  show (TTuple ts) = "(" ++ (tail . init) (show ts) ++ ")"
  show (TFun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TVar n) = show n
  show (TVarName s) = "\'" ++ s
  show (TEither t1 t2) = "Either " ++ show t1 ++ " " ++ show t2

-- 型変数に名前を付ける
{- TVar 0 のような変数を，TVarName 'a' のようなアルファベットの名前に
   置き換えます。足りなくなると a1 b1 ... a2 b2 ... となります。
   これは，OCamlが型変数の名前を付けるときの動作です。
   ここでも(typeinf同様) State モナドを使っています。 -}

type NameStType = (Int, [(TVar,String)])

newtype NameSt a = NameSt { runNameSt :: NameStType -> (a, NameStType) }

instance Monad NameSt where
  return a = NameSt (\s -> (a,s))
  (NameSt f) >>= g = NameSt (\st1 -> let (v, st2) = f st1
                                     in runNameSt (g v) st2)

findStr :: TVar -> NameSt (Maybe String)
findStr v = NameSt (\(n,map) -> (lookup v map, (n,map)))

getAndIncrCount :: NameSt Int
getAndIncrCount = NameSt (\(n,map) -> (n,(n+1,map)))

addName :: TVar -> String -> NameSt ()
addName v s = NameSt (\(n,map) -> ((),(n,(v,s):map)))

nameTVar :: Type -> NameSt Type
nameTVar (TFun t1 t2) = do
  t1' <- nameTVar t1
  t2' <- nameTVar t2
  return (TFun t1' t2')
nameTVar (TList t) = do
  t' <- nameTVar t
  return (TList t')
nameTVar (TTuple ts) = liftM TTuple $ nameTVarTuple ts
nameTVar (TVar v) = do
  maybeS <- findStr v
  case maybeS of
    Just s -> return $ TVarName s
    Nothing -> do
      n <- getAndIncrCount
      let newName = makeName n
      addName v newName
      return $ TVarName $ makeName n
nameTVar TInt = return TInt
nameTVar TBool = return TBool
nameTVar TChar = return TChar
nameTVar TDouble = return TDouble
nameTVar TUnit = return TUnit
nameTVar (TVarName s) = return (TVarName s)
nameTVar (TEither t1 t2) = do
  t1' <- nameTVar t1
  t2' <- nameTVar t2
  return (TEither t1' t2')

nameTVarTuple :: [Type] -> NameSt [Type]
nameTVarTuple [] = return []
nameTVarTuple (t:ts) = do
  t' <- nameTVar t
  ts' <- nameTVarTuple ts
  return (t':ts')

makeName :: Int -> String
makeName n =
  if q == 0 then (dtoc r):""
            else (dtoc r):(show q)
  where
    dtoc n = toEnum (fromEnum 'a' + n)
    r = n `mod` 26
    q = n `div` 26

runNameTVar :: Type -> Type
runNameTVar t = fst $ runNameSt (nameTVar t) (0,[])

instance Show TypeScheme where
  show (ForAll _ t) = show (runNameTVar t)
