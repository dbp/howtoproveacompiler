#!/usr/bin/env stack
-- stack --resolver lts-10.3 --install-ghc runghc --package fn --package warp
{-# LANGUAGE OverloadedStrings #-}
module Compile where

data Arith = Num Integer | Plus Arith Arith | Times Arith Arith

data StackOp = SNum Integer | SPlus | STimes

compile :: [Arith] -> [StackOp]
compile [] = []
compile (Num n:xs) = SNum n : compile xs
compile (Plus a1 a2:xs) = compile [a1] ++ compile [a2] ++ SPlus : compile xs
compile (Times a1 a2:xs) = compile [a1] ++ compile [a2] ++ STimes : compile xs
