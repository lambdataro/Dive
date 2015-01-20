----------------------------------------
--  Main.hs
--
--  新入生SG お手本インタプリタ
--  2012/05/23 高島尚希
----------------------------------------

module Main where

import System.Environment
import System.IO
import Control.Monad

import Syntax
import Parser
import TypeInf
import Eval

main :: IO ()
main = do
  putStrLn "Dive Ver. 0.0.1 (2012/05/23)"
  putStrLn "By Naoki Takashima."
  str <- getSourceFile
  env <- evalStr str initEnv
  return ()

evalStr :: String -> Env -> IO Env
evalStr str env = do
  let expr = runParser str
  let top = runTypeInf expr
  printTopExpr top
  let top' = map (\(a,b,c)->(a,c)) top
  env' <- foldM (\env (x,e) -> evalTop x e env) env top'
  return env'

getSourceFile :: IO String
getSourceFile = do
  args <- getArgs
  putStrLn "----"
  case args of
    [] -> do
      putStrLn "Reading \"test.dive\"."
      readFile "test.dive"
    path:_ -> do 
      putStrLn $ "Reading \"" ++ path ++ "\"."
      readFile path
