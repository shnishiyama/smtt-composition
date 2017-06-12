{-# LANGUAGE OverloadedStrings #-}

module Main where

import ClassyPrelude

import Data.SATT.ATT
import Data.Tree.RankedTree

infixOperators :: InfixOpTree
infixOperators = InfixMulti InfixTwo (InfixPlus (InfixPlus InfixOne InfixTwo) InfixOne)

main :: IO ()
main = do
  print infixOperators

  putStrLn "->"

  let postfixOperators = runAttReduction infixToPostfixTransducer infixOperators
  print postfixOperators
