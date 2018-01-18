#!/usr/bin/env stack
-- stack --resolver lts-10.3 --install-ghc runghc --package fn --package warp
{-# LANGUAGE OverloadedStrings #-}
module Compiler where

data Arith = Num Int
           | Plus Arith Arith
           | Minus Arith Arith
           | Times Arith Arith

data StackOp = SNum Int
             | SPlus
             | SMinus
             | STimes
             deriving Show

eval' :: Arith -> Int
eval' (Num n)       = n
eval' (Plus a1 a2)  = (eval' a1) + (eval' a2)
eval' (Minus a1 a2) = (eval' a1) - (eval' a2)
eval' (Times a1 a2) = (eval' a1) * (eval' a2)

compile :: Arith -> [StackOp]
compile (Num n)       = [SNum n]
compile (Plus a1 a2)  = compile a2 ++ compile a1 ++ [SPlus]
compile (Minus a1 a2) = compile a2 ++ compile a1 ++ [SMinus]
compile (Times a1 a2) = compile a2 ++ compile a1 ++ [STimes]

eval :: [Int] -> [StackOp] -> Either ([Int], [StackOp]) Int
eval (n:_) []               = Right n
eval ns (SNum n:xs)         = eval (n:ns) xs
eval (n1:n2:ns) (SPlus:xs)  = eval (n1+n2:ns) xs
eval (n1:n2:ns) (SMinus:xs) = eval (n1-n2:ns) xs
eval (n1:n2:ns) (STimes:xs) = eval (n1*n2:ns) xs
eval vals instrs            = Left (vals, instrs)
