----------------------------------------
--  TypeInf.hs
--  型推論器
--
--  新入生SG お手本インタプリタ
--  2012/05/23 高島尚希
----------------------------------------

module TypeInf where

import qualified Data.List as List
import Syntax
import System.IO.Unsafe

{- 解説
Algorithm M を実装しています。
参考文献は，Oukseh Lee と Kwangkeun Yi の，
Proofs about a folklore let-polymorphic type inference algorithm です。

新入生SGで扱ったものと異なり，多相型のある型推論です。
多相型の型推論は，京都大学の五十嵐先生の実験資料がわかりやすいです。
-}

{-
型推論では型変数にユニークな整数を割り当てる必要があります。
ここでは，State モナドとよばれるテクニックを使って，
整数の管理をしています。
State モナドやその他のモナドについては，以下のサイトを参考にしてください。
モナドのすべて
http://www.sampou.org/haskell/a-a-monads/html/index.html
-}

newtype TInfSt a = TInfSt { runTInfSt :: Int -> (a, Int) }

instance Monad TInfSt where
  return a = TInfSt (\n -> (a,n))
  (TInfSt f) >>= g = TInfSt (\st1 -> let (v, st2) = f st1
                                     in runTInfSt (g v) st2)

-- 型環境 (変数 x の型 t という情報)
type TEnv = [(Id, TypeScheme)]

-- 型環境から変数を探す
lookupVar :: Id -> TEnv -> TypeScheme
lookupVar x tenv =
  case lookup x tenv of
    Nothing -> error $ "unbound var: " ++ x
    Just t -> t

-- 型代入 (型変数 n は，型 t という情報)
type TSubst = [(TVar, Type)]

-- 型に対して型代入を適用する
subst :: Type -> TSubst -> Type
subst t [] = t
subst (TVar v1) ((v2,t):s)
  {- 同じ型変数が見つかったらそれを適用する。
     まだ未適用の代入があるかもしれないので，再帰的に呼ぶ。 -}
  | v1 == v2 = subst t s
  | otherwise = subst (TVar v1) s
subst (TFun t1 t2) s = TFun (subst t1 s) (subst t2 s)
subst (TEither t1 t2) s = TEither (subst t1 s) (subst t2 s)
subst (TList t) s = TList (subst t s)
subst (TTuple ts) s = TTuple (map (flip subst s) ts)
subst (TVarName _) _ = undefined
subst TInt _ = TInt
subst TBool _ = TBool
subst TChar _ = TChar
subst TDouble _ = TDouble
subst TUnit _ = TUnit

{- 型環境に代入を適用する。 -}
substTEnv :: TEnv -> TSubst -> TEnv
substTEnv tenv s = map f tenv
  where f (v, ForAll fv t) = (v, ForAll fv (subst t s))

-- 新しく型変数を作る
newTVar :: TInfSt Type
newTVar = TInfSt (\n -> (TVar n, n+1))

-- Occurs check (型変数 v が型 t の中に出現すれば True)
occur :: TVar -> Type -> Bool
occur v (TFun t1 t2) = occur v t1 || occur v t2
occur v (TEither t1 t2) = occur v t1 || occur v t2
occur v (TList t) = occur v t
occur v (TTuple ts) = or (map (occur v) ts)
occur v1 (TVar v2) = v1 == v2
occur v TInt = False
occur v TBool = False
occur v TChar = False
occur v TDouble = False
occur v TUnit = False
occur v (TVarName _) = undefined

-- 単一化 (2つの型を等しい型として扱う)
unify :: Type -> Type -> TSubst
{- 型が等しいときは何もしない -}
unify TInt TInt = []
unify TBool TBool = []
unify TUnit TUnit = []
unify TChar TChar = []
unify TDouble TDouble = []
{- 関数: t11 = t21, t12 = t22 にする -}
unify (TTuple ts1) (TTuple ts2) = unifyTuple ts1 ts2
unify (TFun t11 t12) (TFun t21 t22) = s1 ++ s2
  where
    s1 = unify t11 t21
    s2 = unify (subst t12 s1) (subst t22 s1)
unify (TList t1) (TList t2) = unify t1 t2
unify (TEither t11 t12) (TEither t21 t22) =
  unify (TFun t11 t12) (TFun t21 t22) {- fun と同じ -}
{- 全く同じ型変数の時は何もしない -}
unify (TVar v1) (TVar v2)
  | v1 == v2 = []
{- 片方が型変数 v1 の時は，v1 = t2 にする。
   ただし，t2 中に v1 が現れてはいけない。 -}
unify (TVar v1) t2
  | occur v1 t2 = error "occurs error"
  | otherwise = [(v1,t2)]
unify t1 (TVar v2) = unify (TVar v2) t1
{- それ以外はエラー -}
unify t1 t2 =
  error $ "unify error : " ++ show t1 ++ " = " ++ show t2

unifyTuple :: [Type] -> [Type] -> TSubst
unifyTuple [] [] = []
unifyTuple (t1:ts1) (t2:ts2) = s1 ++ s2
  where
    s1 = unifyTuple ts1 ts2
    s2 = unify (subst t1 s1) (subst t2 s1)
unifyTuple ts1 ts2 =
  error $ "unify error (tuple) : " ++ show ts1 ++ " = " ++ show ts2

-- 型スキームの特価
{- 量化された型変数を新しいものに置き換える -}
instantiate :: TypeScheme -> TInfSt Type
instantiate (ForAll qtv t) = do
  tvmap <- makeNewTVars qtv
  return (replaceTVar t tvmap)

{- 型変数に対応する新しい型変数を作る -}
makeNewTVars :: [TVar] -> TInfSt [(TVar,TVar)]
makeNewTVars [] = return []
makeNewTVars (v1:rest) = do
  TVar v2 <- newTVar
  rest' <- makeNewTVars rest
  return ((v1,v2):rest')

{- 型中の型変数をすべて置き換える -}
replaceTVar :: Type -> [(TVar,TVar)] -> Type
replaceTVar (TFun t1 t2) tvmap =
  TFun (replaceTVar t1 tvmap) (replaceTVar t2 tvmap)
replaceTVar (TEither t1 t2) tvmap =
  TEither (replaceTVar t1 tvmap) (replaceTVar t2 tvmap)
replaceTVar (TList t) tvmap = TList (replaceTVar t tvmap)
replaceTVar (TTuple ts) tvmap = TTuple (map (flip replaceTVar tvmap) ts)
replaceTVar (TVar v) tvmap =
  case lookup v tvmap of
    Nothing -> TVar v
    Just v' -> TVar v'
replaceTVar TInt tvmap = TInt
replaceTVar TBool tvmap = TBool
replaceTVar TChar tvmap = TChar
replaceTVar TDouble tvmap = TDouble
replaceTVar TUnit tvmap = TUnit
replaceTVar (TVarName _) tvmap = undefined

-- 型スキームの汎化
{- 量化子 ForAll を付ける -}
generalize :: TEnv -> Type -> TypeScheme
generalize tenv t = ForAll (makeClos t ftv) t
  where ftv = freeTVarsTEnv tenv

{- ForAll を付けるべき型変数を集める -}
makeClos :: Type -> [TVar] -> [TVar]
makeClos (TFun t1 t2) ftv = ftv1 ++ ftv2
  where
    ftv1 = makeClos t1 ftv
    ftv2 = makeClos t2 (ftv ++ ftv1)
makeClos (TEither t1 t2) ftv = makeClos (TFun t1 t2) ftv  {- fun と同じ -}
makeClos (TList t) ftv = makeClos t ftv
makeClos (TTuple ts) ftv = makeClosTuple ts ftv
makeClos (TVar v) ftv
  | elem v ftv = []
  | otherwise = [v]
makeClos TInt _ = []
makeClos TBool _ = []
makeClos TChar _ = []
makeClos TDouble _ = []
makeClos TUnit _ = []
makeClos (TVarName _) _ = undefined

makeClosTuple :: [Type] -> [TVar] -> [TVar]
makeClosTuple [] _ = []
makeClosTuple (t:ts) ftv = ftv1 ++ ftv2
  where 
    ftv1 = makeClos t ftv
    ftv2 = makeClosTuple ts (ftv ++ ftv1)

{- 型スキーム中の自由な型変数を集める -}
freeTVarsTS :: TypeScheme -> [TVar]
freeTVarsTS (ForAll qtv t) = freeTVars qtv t

{- 型中の自由な型変数 -}
freeTVars :: [TVar] -> Type -> [TVar]
freeTVars qtv (TFun t1 t2) = fvs1 ++ fvs2
  where
    fvs1 = freeTVars qtv t1
    fvs2 = freeTVars (qtv ++ fvs1) t2
freeTVars qtv (TEither t1 t2) = freeTVars qtv (TFun t1 t2)  {- fun と同じ -}
freeTVars qtv (TList t) = freeTVars qtv t
freeTVars qtv (TTuple ts) = freeTVarsTuple qtv ts
freeTVars qtv (TVar v)
  | elem v qtv = []
  | otherwise = [v]
freeTVars _ TInt = []
freeTVars _ TBool = []
freeTVars _ TChar = []
freeTVars _ TDouble = []
freeTVars _ TUnit = []
freeTVars _ (TVarName _) = undefined

freeTVarsTuple :: [TVar] -> [Type] -> [TVar]
freeTVarsTuple qtv [] = []
freeTVarsTuple qtv (t:ts) = fvs1 ++ fvs2
  where
    fvs1 = freeTVars qtv t
    fvs2 = freeTVarsTuple (qtv ++ fvs1) ts

{- 型環境中の自由な型変数 -}
freeTVarsTEnv :: TEnv -> [TVar]
{- TEnv の型の部分を取り出して，それぞれの自由な型変数を求め，
   それらを concat でまとめて，nub で重複を除去する。 -}
freeTVarsTEnv tenv = List.nub $ concat $ map freeTVarsTS $ map snd tenv

-- 型推論
typeinf :: Expr -> Type -> TEnv -> TInfSt TSubst
{- アルゴリズムMは，引数に要求される型を持っているので，
   その型と等しいということを，単一化で確認する -}
typeinf (Const (Int _)) t tenv = return (unify TInt t)  {- t は TInt のはず -}
typeinf (Const (Bool _)) t tenv = return (unify TBool t)
typeinf (Const (Char _)) t tenv = return (unify TChar t)
typeinf (Const (Double _)) t tenv = return (unify TDouble t)
typeinf (Const Unit) t tenv = return (unify TUnit t)
typeinf Null t tenv = do
  t1 <- newTVar
  return $ unify t (TList t1)
{- プリミティブ -}
typeinf (Prim p) t1 tenv = do
  t2 <- instantiate (primTs p)
  return (unify t1 t2)
{- 変数 -}
typeinf (Var x) t1 tenv = do
  let ts = lookupVar x tenv
  t2 <- instantiate ts
  return (unify t1 t2)
{- ラムダ式の場合，ここでは，t1 = t2 -> t3 とする。 -}
typeinf (Fun x e) t1 tenv = do
  t2 <- newTVar
  t3 <- newTVar
  let s1 = unify t1 (TFun t2 t3)  {- t1 = t2 -> t3 -}
  {- 次に，x を追加した e における型環境を作る。
     それぞれに，型代入 s1 を適用する必要がある。 -}
  let tenv' = (x, ForAll [] (subst t2 s1)):(substTEnv tenv s1)
  {- e の型推論をする。要求される型は t3 で，t3 にも代入 s1 を適用する。 -}
  s2 <- typeinf e (subst t3 s1) tenv'
  {- 最後に s1 に s2 を適用する -}
  return (s1 ++ s2)
{- 関数適用，ここでは関数の型を t1 -> t2 引数の型を t1，
   そして，全体の型を t2 としています。-}
typeinf (App e1 e2) t2 tenv = do
  t1 <- newTVar
  {- e1 の型推論: 型は t1 -> t2 -}
  s1 <- typeinf e1 (TFun t1 t2) tenv
  {- e2 の型推論: 型は t1 -}
  s2 <- typeinf e2 (subst t1 s1) (substTEnv tenv s1)
  return (s1 ++ s2)
{- let式 -}
typeinf (Let x e1 e2) t2 tenv = do
  t1 <- newTVar
  s1 <- typeinf e1 t1 tenv
  let tenv' = substTEnv tenv s1
  let ts = generalize tenv' (subst t1 s1)
  let tenv2 = (x, ts):tenv'
  s2 <- typeinf e2 (subst t2 s1) tenv2
  return (s1 ++ s2)
{- LetRec式 -}
typeinf (LetRec x e1 e2) t2 tenv = do
  t1 <- newTVar
  s1 <- typeinf e1 t1 ((x, ForAll [] t1):tenv)
  let tenv' = substTEnv tenv s1
  let ts = generalize tenv' (subst t1 s1)
  let tenv2 = (x, ts):tenv'
  s2 <- typeinf e2 (subst t2 s1) tenv2
  return (s1 ++ s2)
{- if -}
typeinf (If e1 e2 e3) t tenv = do
  s1 <- typeinf e1 TBool tenv
  let t' = subst t s1
  let tenv' = substTEnv tenv s1
  s2 <- typeinf e2 t' tenv'
  let t'' = subst t' s2
  let tenv'' = substTEnv tenv' s2
  s3 <- typeinf e3 t'' tenv''
  return (s1 ++ s2 ++ s3)
{- fource -}
typeinf (Force e t1) t2 tenv = do
  let s1 = unify t1 t2
  s2 <- typeinf e (subst t1 s1) (substTEnv tenv s1)
  return (s1 ++ s2)
{- match -}
typeinf (Match e cases) t tenv = do
  t1 <- newTVar
  s1 <- typeinf e t1 tenv
  s2 <- typeinfCaseList cases (subst t1 s1) (subst t s1) (substTEnv tenv s1)
  return (s1 ++ s2)
{- Tuple -}
typeinf (Tuple es) t tenv = do
  ts <- mapM (\_ -> newTVar) es
  s1 <- typeinfTupleList es ts tenv
  let s2 = unify (subst t s1) (TTuple (map (flip subst s1) ts))
  return (s1 ++ s2)

typeinfTupleList :: [Expr] -> [Type] -> TEnv -> TInfSt TSubst
typeinfTupleList [] [] tenv = return []
typeinfTupleList (e:es) (t:ts) tenv = do
  s1 <- typeinf e t tenv
  s2 <- typeinfTupleList es (map (flip subst s1) ts) (substTEnv tenv s1)
  return (s1 ++ s2)
typeinfTupleList _ _ _ = error "typing error (tuple)"

typeinfCaseList :: [(Pat,Expr,Expr)] -> Type -> Type -> TEnv -> TInfSt TSubst
typeinfCaseList [] pt bt tenv = return []
typeinfCaseList (c:cs) pt bt tenv = do
  s1 <- typeinfCase c pt bt tenv
  s2 <- typeinfCaseList cs (subst pt s1) (subst bt s1) (substTEnv tenv s1)
  return (s1 ++ s2)

typeinfCase :: (Pat, Expr, Expr) -> Type -> Type -> TEnv -> TInfSt TSubst
typeinfCase (pat, gird, body) pt bt tenv = do
  (s1, e1) <- typeinfPat pat pt tenv
  let e1' = checkPatVars e1  {- e1 に重複した変数が無いことを確認する -}
  let env' = e1' ++ substTEnv tenv s1
  s2 <- typeinf gird TBool env'
  let bt' = subst (subst bt s1) s2
  s3 <- typeinf body bt' (substTEnv env' s2)
  return (s1 ++ s2 ++ s3)

{- パターンの型推論, 代入と新たな環境を返す -}
typeinfPat :: Pat -> Type -> TEnv -> TInfSt (TSubst, TEnv)
typeinfPat PWild t tenv = return ([], [])
typeinfPat (PVar x) t tenv = return ([], [(x, ForAll [] t)])
typeinfPat (PConst (Int _)) t tenv = return (unify t TInt, [])
typeinfPat (PConst (Bool _)) t tenv = return (unify t TBool, [])
typeinfPat (PConst (Char _)) t tenv = return (unify t TChar, [])
typeinfPat (PConst (Double _)) t tenv = return (unify t TDouble, [])
typeinfPat (PConst Unit) t tenv = return (unify t TUnit, [])
typeinfPat PNull t tenv = do
  t1 <- newTVar
  return (unify t (TList t1), [])
typeinfPat (PCons p1 p2) t tenv = do
  t1 <- newTVar
  let s1 = unify t (TList t1)
  let t1' = subst t1 s1
  let tenv' = substTEnv tenv s1
  (s2,e2) <- typeinfPat p1 t1' tenv'
  (s3,e3) <- typeinfPat p2 (subst (TList t1') s2)(substTEnv tenv' s2)
  let renv = substTEnv e2 s3 ++ e3
  return (s1 ++ s2 ++ s3, renv)
typeinfPat (PTuple ps) t tenv = do
  ts <- mapM (\_ -> newTVar) ps
  (s,e) <- typeinfPatTuple ps ts tenv
  let s2 = unify (subst t s) (TTuple (map (flip subst s) ts))
  return (s ++ s2, substTEnv e s2)
typeinfPat (PLeft p) t tenv = do
  t1 <- newTVar
  t2 <- newTVar
  (s1,e1) <- typeinfPat p t1 tenv
  let s2 = unify (subst t s1) (TEither (subst t1 s1) (subst t2 s1))
  return (s1 ++ s2, substTEnv e1 s2)
typeinfPat (PRight p) t tenv = do
  t1 <- newTVar
  t2 <- newTVar
  (s1,e1) <- typeinfPat p t2 tenv
  let s2 = unify (subst t s1) (TEither (subst t1 s1) (subst t2 s1))
  return (s1 ++ s2, substTEnv e1 s2)

typeinfPatTuple :: [Pat] -> [Type] -> TEnv -> TInfSt (TSubst, TEnv)
typeinfPatTuple [] [] _ = return ([],[])
typeinfPatTuple (p:ps) (t:ts) tenv = do
  (s1,e1) <- typeinfPat p t tenv
  (s2,e2) <- typeinfPatTuple ps (map (flip subst s1) ts) (substTEnv tenv s1)
  return (s1 ++ s2, substTEnv e1 s2 ++ e2)
typeinfPatTuple _ _ _ = error "typing error (tuple pattern)"

checkPatVars :: TEnv -> TEnv
checkPatVars tenv =
  {- e2 と e3 に同じ変数名があるときはエラー -}
  if (tenv /= [] &&
       (maximum $ map length $ List.group $ map fst tenv) > 1)
    then error "same name in a pattern"
    else tenv

-- プリミティブ関数の型スキーム
primTs :: PrimId -> TypeScheme
primTs Neg = ForAll [] (TFun TInt TInt)
primTs Not = ForAll [] (TFun TBool TBool)
primTs FNeg = ForAll [] (TFun TDouble TDouble)
primTs Add = tsIntOp
primTs Sub = tsIntOp
primTs Mul = tsIntOp
primTs Div = tsIntOp
primTs Mod = tsIntOp
primTs FAdd = tsDoubleOp
primTs FSub = tsDoubleOp
primTs FMul = tsDoubleOp
primTs FDiv = tsDoubleOp
primTs Lt = tsCmpOp
primTs Gt = tsCmpOp
primTs Le = tsCmpOp
primTs Ge = tsCmpOp
primTs Eq = tsCmpOp
primTs Ne = tsCmpOp
primTs And = tsBoolOp
primTs Or = tsBoolOp
primTs Cons = ForAll [0] (TFun (TVar 0) (TFun (TList (TVar 0)) (TList (TVar 0))))
primTs Append = ForAll [0] (TFun (TList (TVar 0)) (TFun (TList (TVar 0)) (TList (TVar 0))))
primTs MakeLeft = ForAll [0,1] (TFun (TVar 0) (TEither (TVar 0) (TVar 1)))
primTs MakeRight = ForAll [0,1] (TFun (TVar 1) (TEither (TVar 0) (TVar 1)))
primTs Print = ForAll [0] (TFun (TVar 0) TUnit)
primTs Ord = ForAll [] (TFun TChar TInt)
primTs Chr = ForAll [] (TFun TInt TChar)
primTs ToInt = ForAll [] (TFun TDouble TInt)
primTs ToDouble = ForAll [] (TFun TInt TDouble)

tsIntOp :: TypeScheme
tsIntOp = ForAll [] (TFun TInt (TFun TInt TInt))

tsBoolOp :: TypeScheme
tsBoolOp = ForAll [] (TFun TBool (TFun TBool TBool))

tsDoubleOp :: TypeScheme
tsDoubleOp = ForAll [] (TFun TDouble (TFun TDouble TDouble))

tsCmpOp :: TypeScheme
tsCmpOp = ForAll [0] (TFun (TVar 0) (TFun (TVar 0) TBool))

typeInfTop :: TopExpr -> TEnv -> TInfSt TopExpr
typeInfTop [] _ = return []
typeInfTop ((x,_,e):rest) tenv = do
  t <- newTVar
  s <- typeinf e t ((x, ForAll [] t):tenv)
  -- let tenv' = substTEnv tenv s
  let t' = subst t s
  let ts = generalize [] t' -- 空の環境でgeneralize
  if freeTVarsTS ts /= []
    then error $ x ++ " has free variable"
    else do
      rest' <- typeInfTop rest $ (x,ts):tenv
      return $ (x,show ts,e):rest'

initTEnv :: TopExpr
initTEnv = [ ("not", "", Prim Not),
             ("Left", "", Prim MakeLeft),
             ("Right", "", Prim MakeRight),
             ("print", "", Prim Print),
             ("ord", "", Prim Ord),
             ("chr", "", Prim Chr),
             ("toInt", "", Prim ToInt),
             ("toDouble", "", Prim ToDouble) ]

runTypeInf :: TopExpr -> TopExpr
runTypeInf top =
  drop (length initTEnv) $
    fst $ runTInfSt (typeInfTop (initTEnv ++ top) []) 0
