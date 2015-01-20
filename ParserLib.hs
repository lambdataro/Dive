----------------------------------------
--  ParserLib.hs
--  パーサコンビネータライブラリ
--
--  新入生SG お手本インタプリタ
--  2012/05/23 高島尚希
----------------------------------------

module ParserLib where

import Control.Monad
import Control.Applicative hiding (many)
import qualified Control.Applicative as Applicative

{- 解説
Graham Hutton と Erik Meijer の
Functional Pearls Monadic Parsing in Haskell の実装です。
-}

newtype Parser a = Parser { parse :: String -> [(a,String)] }

{- 上のように書くと，parse 関数を自動で定義してくれます。 -}

instance Monad Parser where
  return a = Parser (\cs -> [(a,cs)])
  (Parser p) >>= f = Parser (\cs -> concat [parse (f a) cs' | (a,cs') <- p cs])

{- 上の定義では，パターンマッチで parse 関数の利用を一回減らしています。 -}

instance MonadPlus Parser where
  mzero = Parser (\cs -> [])
  p `mplus` q = Parser (\cs -> parse p cs ++ parse q cs)

(+++) :: Parser a -> Parser a -> Parser a
p +++ q = Parser (\cs -> case parse (p `mplus` q) cs of
                           [] -> []
                           (x:xs) -> [x])

{- ここでは，Monad, MonadPlus に加えて，Parser を，
   Functor, Applicative, Alternative のインスタンスにしています。
   Applicative の説明は，山本和彦さんの以下のブログが詳しいです。
   あどけない話 - Applicativeのススメ
   http://d.hatena.ne.jp/kazu-yamamoto/20101211/1292021817
-}

instance Functor Parser where
  fmap = liftM

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Alternative Parser where
  empty = mzero
  (<|>) = (+++)

{- (+++) の代わりに (<|>) を使うと，より BNF に近い表記になります。 -}


{- 基本的なパーサ -}

item :: Parser Char
item = Parser (\cs -> case cs of
                        "" -> []
                        (c:cs) -> [(c,cs)])

sat :: (Char -> Bool) -> Parser Char
sat p = do { c <- item; if p c then return c else mzero }

char :: Char -> Parser Char
char c = sat (c ==)

string :: String -> Parser String
string "" = return ""
string (c:cs) = do { char c; string cs; return (c:cs) }


{- 上で Applicative のインスタンスにしたので，
   many と many1 をタダで手に入れることができます。 -}

many :: Parser a -> Parser [a]
many = Applicative.many

many1 :: Parser a -> Parser [a]
many1 = some

sepby, sepby1 :: Parser a -> Parser b -> Parser [a]
p `sepby` sep = (p `sepby1` sep) +++ return []
p `sepby1` sep = do a <- p
                    as <- many (do {sep; p})
                    return (a:as)

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) +++ return a

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do { a <- p; rest a }
                 where
                   rest a = (do f <- op
                                b <- p
                                rest (f a b))
                            +++ return a

{- ついでに，右結合の演算子コンビネータ chainr と chainr1 も作っておきます。 -}

chainr :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr p op a = (p `chainr1` op) +++ return a

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainr1` op = do { a <- p; rest a }
                 where
                   rest a = (do f <- op
                                b <- p `chainr1` op
                                return (f a b))
                            +++ return a

{- 最後に，論文には載っていない notFollowedBy コンビネータを定義します。
   これは，パーサが失敗したら成功するコンビネータです。 -}
notFollowedBy :: Parser a -> Parser ()
notFollowedBy p = Parser (\cs -> case parse p cs of
                                   [] -> [((),cs)]
                                   _ -> [])
