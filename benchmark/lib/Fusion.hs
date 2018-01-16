module Fusion where

import           SattPrelude

import           Control.Bench
import           Control.Monad.State
import           Criterion
import           System.Random

import           Samples.Instances
import           Samples.PostfixOpParser

testCases :: NFData b => [(String, a)] -> (a -> b) -> [(Benchmark, NameableWeigh)]
testCases cases f = [ nmItem nm (nf f x, nameableWeighFunc f x) | (nm, x) <- cases ]

evalRandomState :: Int -> State StdGen a -> a
evalRandomState i s = evalState s $ mkStdGen i

nextRandomState :: State StdGen Int
nextRandomState = do
  g <- get
  let (i, g') = next g
  put g'
  pure i

buildInfixOpTree :: Int -> State StdGen InfixOpTree
buildInfixOpTree n
  | n < 1 || n `mod` 2 == 0 = error "negative or even number"
  | otherwise = go $ n `div` 2
  where
    go 0 = do
      i <- nextRandomState
      pure $ [ InfixOneNode, InfixTwoNode ] `indexEx` (i `mod` 2)
    go m = do
      i <- nextRandomState
      let nodef = [ InfixMultiNode, InfixPlusNode ] `indexEx` (i `mod` 2)
      j <- (`mod` m) <$> nextRandomState
      lnode <- go j
      rnode <- go $ m - j - 1
      pure $ nodef lnode rnode

buildPostfixOpTree :: Int -> State StdGen PostfixOpTree
buildPostfixOpTree n = itop <$> buildInfixOpTree n

infixOpTreeCases :: [(String, InfixOpTree)]
infixOpTreeCases =
  [ (show n, evalRandomState 0 $ buildInfixOpTree $ 2 * n + 1)
  | n <- [100, 250, 500, 1500]
  ]

postfixOpTreeCases :: [(String, PostfixOpTree)]
postfixOpTreeCases =
  [ (show n, evalRandomState 0 $ buildPostfixOpTree $ 2 * n + 1)
  | n <- [200, 500, 1000, 3000]
  ]

benchSpec :: ([Benchmark], [NameableWeigh])
benchSpec = unzip
  [ nmGroup "itop-reverse"
    [ nmGroup "normal" $ testCases infixOpTreeCases $ itop >>> reversePop
    , nmGroup "fusion" $ testCases infixOpTreeCases itopReversePop
    , nmGroup "fusionOrig" $ testCases infixOpTreeCases itopReversePopOrig
    ]
  , nmGroup "ptoi-twoCounter"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ ptoi >>> twoCounter
    , nmGroup "fusion" $ testCases postfixOpTreeCases ptoiTwoCounter
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases ptoiTwoCounterOrig
    ]
  , nmGroup "ptoi-itop"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ ptoi >>> itop
    , nmGroup "fusion" $ testCases postfixOpTreeCases ptoiItop
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases ptoiItopOrig
    ]
  ]
