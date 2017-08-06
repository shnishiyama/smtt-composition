{-# LANGUAGE OverloadedStrings #-}

module Main where

import ClassyPrelude

import Data.SATT.Demo

main :: IO ()
main = do
  print postfixOpTreeSample

  putStrLn "->"

  let postfixOperators = treeTrans (infixToPostfixTransducer `composeSatts` postfixToInfixTransducer) postfixOpTreeSample
  print postfixOperators
