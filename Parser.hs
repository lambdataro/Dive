----------------------------------------
--  Parser.hs
--  構文解析器
--
--  新入生SG お手本インタプリタ
--  2012/05/23 高島尚希
----------------------------------------

module Parser (runParser) where

import Data.Char
import Control.Monad
import Control.Applicative hiding (Const, many)
import Syntax
import ParserLib

--------------------------------
-- 構文解析の開始
--------------------------------
runParser :: String -> TopExpr
runParser str =
  case apply (many topExpr) str of
    (e,""):_ -> e
    _ -> error "syntax error"

--------------------------------
-- トップレベル式
--------------------------------

topExpr :: Parser (Id,String,Expr)
topExpr = topDo <|> topLet

-- f x1 x2 ... = e;
topLet :: Parser (Id,String,Expr)
topLet = do
  name <- ident
  args <- many ident
  symb "="
  body <- expr
  symb ";"
  {- トップレベル式の型は型推論で代入する -}
  return (name, "", argList args body)

-- e;
topDo :: Parser (Id,String,Expr)
topDo = do { e <- expr; symb ";"; return ("it", "", e) }

-- 入れ子のFunを作る
argList :: [String] -> Expr -> Expr
argList [] e = e
argList (x:xs) e = Fun x (argList xs e)

--------------------------------
-- 式 (優先度10)
--------------------------------
expr :: Parser Expr
expr =  letrecExpr <|> letExpr {- letrec を let の前に置くこと -}
    <|> funExpr <|> ifExpr <|> matchExpr <|> infixFun

-- let x = e in e
letExpr :: Parser Expr
letExpr = f <$> (symb "let" *> ident) <*> (many ident)
            <*> (symb "=" *> expr) <*> (symb "in" *> expr)
  where f x xs e1 e2 = LetRec x (argList xs e1) e2

-- let rec x = e in e
letrecExpr :: Parser Expr
letrecExpr = f <$> (symb "let" *> symb "rec" *> ident)
               <*> (many ident) <*> (symb "=" *> expr) <*> (symb "in" *> expr)
  where f x xs e1 e2 = LetRec x (argList xs e1) e2

-- \x -> e
funExpr :: Parser Expr
funExpr = argList <$> (symb "fun" *> many1 ident) <*> (symb "->" *> expr)

-- if e then e else e
ifExpr :: Parser Expr
ifExpr = If <$> (symb "if" *> expr) <*> (symb "then" *> expr) <*> (symb "else" *> expr)

-- match 
matchExpr :: Parser Expr
matchExpr = Match <$> (symb "match" *> expr <* symb "{")
                  <*> ((matchCase `sepby1` symb ";") <* option (symb ";") <* symb "}")

matchCase :: Parser (Pat, Expr, Expr)
matchCase =  case1 <$> patExpr <*> (symb "when" *> expr) <*> (symb "->" *> expr)
         <|> case2 <$> patExpr <*> (symb "->" *> expr)
  where case1 p e1 e2 = (p, e1, e2)
        case2 p e = (p, Const (Bool True), e)


--------------------------------
-- 関数の中置 (優先度9)
--------------------------------

-- e `f`e
infixFun :: Parser Expr
infixFun = boolOpExpr `chainl1` infixFunOp

infixFunOp :: Parser (Expr -> Expr -> Expr)
infixFunOp = (\x e1 e2 -> App (App x e1) e2)
              <$> (symb "`" *> variable <* symb "`")

--------------------------------
-- Bool演算 (優先度8)
--------------------------------

-- e && e | e || e
boolOpExpr :: Parser Expr
boolOpExpr = cmpExpr `chainl1` boolOp

boolOp :: Parser (Expr -> Expr -> Expr)
boolOp = infixOp "&&" And <|> infixOp "||" Or

--------------------------------
-- 比較演算 (優先度7)
--------------------------------
-- e <= e | e < e | e >= e | e > e | e == e | e /= e
cmpExpr :: Parser Expr
cmpExpr = consExpr `chainl1` cmpOp

cmpOp :: Parser (Expr -> Expr -> Expr)
cmpOp =  infixOp "<=" Le <|> infixOp ">=" Ge
     <|> infixOp "<"  Lt <|> infixOp ">"  Gt
     <|> infixOp "==" Eq <|> infixOp "/=" Ne

--------------------------------
-- リスト演算 (優先度6)
--------------------------------
-- e : e | e ++ e
consExpr :: Parser Expr
consExpr = addExpr `chainr1` consOp

consOp :: Parser (Expr -> Expr -> Expr)
consOp =  infixOp ":" Cons <|> infixOp "++" Append

--------------------------------
-- 加算 (優先度5)
--------------------------------
-- e + e
addExpr :: Parser Expr
addExpr = mulExpr `chainl1` addOp

addOp :: Parser (Expr -> Expr -> Expr)
addOp =  infixOp "+." FAdd <|> infixOp "-." FSub
     <|> infixOp "+" Add <|> infixOp "-" Sub

--------------------------------
-- 減算 (優先度4)
--------------------------------
-- e * e
mulExpr :: Parser Expr
mulExpr = unaryExpr `chainl1` do { symb "*"; return (primApp2 Mul) }

mulOp :: Parser (Expr -> Expr -> Expr)
mulOp =  infixOp "*." FMul <|> infixOp "/." FDiv
     <|> infixOp "*" Mul <|> infixOp "/" Div <|> infixOp "%" Mod

--------------------------------
-- 単項演算子 (優先度3)
--------------------------------
-- -(e)
unaryExpr :: Parser Expr
unaryExpr =  (primApp1 Neg <$> (symb "-" *> appExpr))
         <|> (primApp1 FNeg <$> (symb ".-" *> appExpr))
         <|> appExpr

--------------------------------
-- 関数適用 (優先度2)
--------------------------------
-- e e
appExpr :: Parser Expr
appExpr = factor `chainl1` return App

--------------------------------
-- 因子 (優先度1)
--------------------------------
-- c | ( e )
factor :: Parser Expr
factor = consts <|> variable <|> opFun <|> forceType <|> tuple
      <|> listLit <|> nullList <|> stringLit <|> parens expr <|> seqExpr

-- 変数
variable :: Parser Expr
variable = Var <$> ident

-- 型を強制 (e :: t)
forceType :: Parser Expr
forceType = parens $ do
  e <- expr
  symb "::"
  t <- typeExpr
  return (Force e t)

-- 定数
consts :: Parser Expr
{- doubleLit を integer より前にする -}
consts = doubleLit <|> integerLit <|> boolean <|> charLit <|> unitLit

-- ユニット()
unitLit :: Parser Expr
unitLit = (symb "(" *> symb ")" *> return (Const Unit))

--------------------------------
-- 括弧で囲んだ演算子
--------------------------------
opFun :: Parser Expr
opFun =  parens (symb "++" *> return (Prim Append))
     <|> parens (symb ":" *> return (Prim Cons))
     <|> parens (symb "+." *> return (Prim FAdd))
     <|> parens (symb "-." *> return (Prim FSub))
     <|> parens (symb "*." *> return (Prim FMul))
     <|> parens (symb "/." *> return (Prim FDiv))
     <|> parens (symb "+" *> return (Prim Add))
     <|> parens (symb "-" *> return (Prim Sub))
     <|> parens (symb "*" *> return (Prim Mul))
     <|> parens (symb "/" *> return (Prim Div))
     <|> parens (symb "%" *> return (Prim Mod))
     <|> parens (symb "<" *> return (Prim Lt))
     <|> parens (symb ">" *> return (Prim Gt))
     <|> parens (symb "<=" *> return (Prim Le))
     <|> parens (symb ">=" *> return (Prim Ge))
     <|> parens (symb "/=" *> return (Prim Ne))
     <|> parens (symb "==" *> return (Prim Eq))
     <|> parens (symb "&&" *> return (Prim And))
     <|> parens (symb "||" *> return (Prim Or))

--------------------------------
-- 逐次処理
--------------------------------
seqExpr :: Parser Expr
seqExpr = do
  symb "{"
  body <- expr `chainl1` (symb ";" >> return makeSeq)
  option (symb ";")
  symb "}"
  return body

makeSeq :: Expr -> Expr -> Expr
makeSeq e1 e2 = App (Fun "{dummy}" e2) e1

--------------------------------
-- タプル
--------------------------------
tuple :: Parser Expr
tuple = do
  symb "("
  e <- expr
  symb ","
  es <- expr `sepby1` (symb ",")
  symb ")"
  return (Tuple (e:es))

--------------------------------
-- リスト
--------------------------------
-- 空リスト
nullList :: Parser Expr
nullList = symb "[" *> symb "]" *> return Null

-- リストリテラル [e1, e2, ... ]
listLit :: Parser Expr
listLit = toCons <$> (symb "[" *> expr `sepby1` symb "," <* symb "]")
  where
    toCons [] = Null
    toCons (e:es) = primApp2 Cons e $ toCons es

--------------------------------
-- リテラル
--------------------------------

-- Double定数
doubleLit :: Parser Expr
doubleLit = makeDouble <$> many1 digit <*> (dpars1 <|> dpars2 <|> dpars3) <* space
  where
    -- 1.23e-3
    dpars1 = do { d <- decimal; e <- exponent; return (d ++ "e" ++ e) }
    -- 1.23
    dpars2 = decimal
    -- 123e-3
    dpars3 = do { e <- exponent; return ( "0e" ++ e) }
    decimal = char '.' *> many1 digit
    exponent = do
      (char 'e' <|> char 'E')
      c <- (char '+' <|> char '-' <|> return '+')
      cs <- many1 digit
      return (c:cs)
    makeDouble i d = Const $ Double $ read $ i ++ "." ++ d

-- 整数定数
integerLit :: Parser Expr
integerLit =
  char '0' *> (
    (char 'x' <|> char 'X') *> (strToInt 16 <$> many1 (sat isHexDigit))
    <|>
    (char 'o' <|> char 'O') *> (strToInt 8 <$> many1 (sat isOctDigit))
    <|>
    (char 'b' <|> char 'B') *> (strToInt 2 <$> many1 (char '0' <|> char '1'))
    <|>
    (char 'd' <|> char 'D') *> (strToInt 10 <$> many1 (sat isDigit))
    <|>
    return (Const (Int 0))
  ) <* space
  <|>
  strToInt 10 <$> (many1 digit <* space)
  where
    strToInt base str =
      Const $ Int $ foldl (\a c -> a * base + digitToInt c) 0 str

-- Bool定数
boolean :: Parser Expr
boolean = (symb "True" >> return (Const $ Bool True)) <|>
          (symb "False" >> return (Const $ Bool False))

-- Char定数
charLit :: Parser Expr
charLit = do
  char '\''
  c <- (char '\\' *> (escape <$> item) <|> item)
  char '\''
  space
  return (Const (Char c))

-- 文字列
stringLit :: Parser Expr
stringLit =
  do
    char '\"'
    str <- many $ notFollowedBy (char '\"') *> (char '\\' *> (escape <$> item) <|> item)
    char '\"'
    space
    return (toCons str)
  where 
    toCons "" = Null
    toCons (c:cs) =
      primApp2 Cons (Const (Char c)) (toCons cs)

-- エスケープシーケンスの変換
escape :: Char -> Char
escape 'n' = '\n'
escape 'r' = '\r'
escape 't' = '\t'
escape 'b' = '\b'
escape c   = c

--------------------------------
-- パターン
--------------------------------

-- 優先度3
patExpr :: Parser Pat
patExpr = patTerm `chainr1` (symb ":" *> return PCons)

-- 優先度2
patTerm :: Parser Pat
patTerm = patEither <|> patFactor

-- 優先度1
patFactor :: Parser Pat
patFactor =  symb "_" *> return PWild
         <|> PVar <$> ident
         <|> toPConst <$> consts
         <|> symb "[" *> symb "]" *> return PNull
         <|> patTuple
         <|> patList
         <|> patEither
         <|> parens patExpr
  where toPConst (Const id) = PConst id
        toPConst _ = undefined

-- タプルパターン
patTuple :: Parser Pat
patTuple = do
  symb "("
  p <- patExpr
  symb ","
  ps <- patExpr `sepby1` symb ","
  symb ")"
  return (PTuple (p:ps))

-- リストパターン
patList :: Parser Pat
patList = toPCons <$> (symb "[" *> patExpr `sepby1` symb "," <* symb "]")
  where
    toPCons [] = PNull
    toPCons (p:ps) = PCons p (toPCons ps)

-- Either パターン
patEither :: Parser Pat
patEither =  PLeft <$> (symb "Left" *> patFactor)
         <|> PRight <$> (symb "Right" *> patFactor)

--------------------------------
-- 型
--------------------------------

-- 優先度2
typeExpr :: Parser Type
typeExpr = typeFactor `chainr1` (symb "->" *> return TFun)
        <|> TEither <$> (symb "Either" *> typeFactor) <*> typeFactor

-- 優先度1
typeFactor :: Parser Type
typeFactor =  symb "Int" *> return TInt
          <|> symb "Bool" *> return TBool
          <|> symb "Char" *> return TChar
          <|> symb "Double" *> return TDouble
          <|> symb "(" *> symb ")" *> return TUnit
          <|> TList <$> (symb "[" *> typeExpr <* symb "]")
          <|> parens typeExpr {- tuple より上に配置 -}
          <|> TTuple <$> (symb "(" *> typeExpr `sepby1` symb ","  <* symb ")")

--------------------------------
-- 式に関するコンビネータ
--------------------------------

-- 中置演算子を作る
infixOp :: String -> PrimId -> Parser (Expr -> Expr -> Expr)
infixOp s p = symb s *> return (primApp2 p)

-- 1引数プリミティブへの適用
primApp1 :: PrimId -> Expr -> Expr
primApp1 p e = App (Prim p) e

-- 2引数プリミティブへの適用
primApp2 :: PrimId -> Expr -> Expr -> Expr
primApp2 p e1 e2 = App (App (Prim p) e1) e2

-- 識別子
ident :: Parser Id
ident = do
  c <- alpha <|> char '_'
  cs <- many (alphaNum <|> char '_' <|> char '\'')
  space
  if elem (c:cs) keyWdList
    then mzero
    else return (c:cs)

-- キーワードのリスト (型はキーワードに入れない)
keyWdList :: [String]
keyWdList = [ "let", "in", "True", "False", "fun", "rec",
              "if", "then", "else", "match", "when" ]

-- 括弧を付ける
parens :: Parser a -> Parser a
parens p = symb "(" *> p <* symb ")"

-- 省略可能
option :: Parser a -> Parser ()
option p = (p *> return ()) <|> return ()

--------------------------------
-- 空白・コメント
--------------------------------

-- パーサの戻り値を () にする
retUnit :: Parser a -> Parser ()
retUnit p = p >> return ()

-- コメントと空白
space :: Parser ()
space = retUnit (white `sepby` comment)

-- 空白
white :: Parser ()
white = retUnit $ many (sat isSpace)

-- コメント
comment :: Parser ()
comment = lineComment <|> nestComment

-- 単一行コメント
lineComment :: Parser ()
lineComment = retUnit $ string "--" >> many (sat (/= '\n'))

-- 入れ子コメント
nestComment :: Parser ()
nestComment = do
  string "{-"
  many $ notFollowedBy (string "-}") >> (nestComment <|> retUnit item)
  retUnit $ string "-}"

-- 後ろのスペースを取り除く
token :: Parser a -> Parser a
token p = do { a <- p; space; return a }

-- 文字の読み取りとスペースの取り除き
symb :: String -> Parser String
symb cs = token (string cs)

-- 最初のスペースを取り除く
apply :: Parser a -> String -> [(a,String)]
apply p = parse (do { space; p })

--------------------------------
-- 文字のパーサ
--------------------------------
digit :: Parser Char
digit = sat isDigit

alpha :: Parser Char
alpha = sat isAlpha

alphaNum :: Parser Char
alphaNum = sat isAlphaNum
