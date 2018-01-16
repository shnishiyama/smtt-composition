module Main where

import           Criterion.Main
import           SattPrelude

import           Fusion
import           Samples.Instances

main :: IO ()
main = defaultMain
  [ bench "ptoiItop" $ nf ptoiItop inputPostfixTree
  ]
  where
    inputPostfixTree = evalRandomState 0 $ buildPostfixOpTree $ 2 * 1500 + 1
