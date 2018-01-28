{-# OPTIONS_GHC -Wno-unused-imports #-}

module Main where

import           Criterion.Main
import           SattPrelude

import           Fusion
import           Samples.Instances
import           Samples.PostfixOpParser

main :: IO ()
main = do
    print $ length $ show $ ptoiItop inputPostfixTree
  where
    inputPostfixTree = build (2 * 1500 + 1 :: Int) PostfixEndNode

    build n
      | n <  1     = error "not positive number"
      | otherwise  = go n
      where
        go 1 e = PostfixOneNode e
        go m e = go (m - 1) $ PostfixOneNode $ PostfixMultiNode e
