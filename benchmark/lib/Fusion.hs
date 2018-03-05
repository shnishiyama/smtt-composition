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
      i <- mod <$> nextRandomState <*> pure 2
      pure $ [ InfixOneNode, InfixTwoNode ] `indexEx` i
    go m = do
      i <- mod <$> nextRandomState <*> pure 2
      let nodef = [ InfixMultiNode, InfixPlusNode ] `indexEx` i
      j <- mod <$> nextRandomState <*> pure m
      lnode <- go j
      rnode <- go $ m - j - 1
      pure $ nodef lnode rnode

buildLinearInfixOpTree :: Int -> State StdGen InfixOpTree
buildLinearInfixOpTree n
  | n < 1     = error "non positive number"
  | otherwise = go n
  where
    go 1 = do
      i <- mod <$> nextRandomState <*> pure 2
      pure $ [ InfixOneNode, InfixTwoNode ] `indexEx` i
    go m = do
      i <- mod <$> nextRandomState <*> pure 2
      let nodef = [ InfixMultiNode, InfixPlusNode ] `indexEx` i
      j <- mod <$> nextRandomState <*> pure 2
      let lnode = [ InfixOneNode, InfixTwoNode ] `indexEx` j
      rnode <- go $ m - 1
      pure $ nodef lnode rnode

buildPostfixOpTree :: Int -> State StdGen PostfixOpTree
buildPostfixOpTree n = itop <$> buildInfixOpTree n

infixOpTreeCases :: [(String, InfixOpTree)]
infixOpTreeCases =
  [ (show n, evalRandomState 0 $ buildInfixOpTree $ 2 * n + 1)
  | n <- [100, 250, 500, 1500]
  ]

postfixOpTreeCases :: [(String, PostfixOpTree)]
postfixOpTreeCases = do
  n <- [100, 250, 500, 1500]
  let case1 = ("random-" <> show n, evalRandomState 0 $ buildPostfixOpTree $ 2 * n + 1)
  [ case1 ]

benchSpec :: ([Benchmark], [NameableWeigh])
benchSpec = unzip
  [ nmGroup "itop-reverse"
    [ nmGroup "normal" $ testCases infixOpTreeCases $ itop >>> reversePop
    , nmGroup "fusion" $ testCases infixOpTreeCases itopReversePop
    , nmGroup "fusionOrig" $ testCases infixOpTreeCases itopReversePopOrig
    ]
  {-, nmGroup "ptoi-twoCounter"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ ptoi >>> twoCounter
    , nmGroup "fusion" $ testCases postfixOpTreeCases ptoiTwoCounter
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases ptoiTwocounterOrig
    ] -}
  , nmGroup "ptoi-itop"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ ptoi >>> itop
    , nmGroup "fusion" $ testCases postfixOpTreeCases ptoiItop
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases ptoiItopOrig
    --, nmGroup "fusionWalk" $ testCases postfixOpTreeCases ptoiItopWalk
    ]
  , nmGroup "ptoi-depth"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ ptoi >>> depthRightSide
    , nmGroup "fusion" $ testCases postfixOpTreeCases ptoiDepth
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases ptoiDepthOrig
    ]
  , nmGroup "ptoi-flat"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ ptoi >>> flatRightSide
    , nmGroup "fusion" $ testCases postfixOpTreeCases ptoiFlat
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases ptoiFlatOrig
    ]
  ]
