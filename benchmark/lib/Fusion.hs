module Fusion where

import           SmttPrelude

import           Control.Bench
import           Control.Monad.State
import           Criterion
import           System.Random

import           Samples.Instances
import           Samples.TermOpParser
import           Samples.Fusions

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

buildInfixOpTree :: Int -> State StdGen ITerm
buildInfixOpTree n
  | n < 1 || n `mod` 2 == 0 = error "negative or even number"
  | otherwise = go $ n `div` 2
  where
    go 0 = do
      i <- mod <$> nextRandomState <*> pure 2
      pure $ [ IOne, ITwo ] `indexEx` i
    go m = do
      i <- mod <$> nextRandomState <*> pure 2
      let nodef = [ IMult, IPlus ] `indexEx` i
      j <- mod <$> nextRandomState <*> pure m
      lnode <- go j
      rnode <- go $ m - j - 1
      pure $ nodef lnode rnode

buildLinearInfixOpTree :: Int -> State StdGen ITerm
buildLinearInfixOpTree n
  | n < 1     = error "non positive number"
  | otherwise = go n
  where
    go 1 = do
      i <- mod <$> nextRandomState <*> pure 2
      pure $ [ IOne, ITwo ] `indexEx` i
    go m = do
      i <- mod <$> nextRandomState <*> pure 2
      let nodef = [ IMult, IPlus ] `indexEx` i
      j <- mod <$> nextRandomState <*> pure 2
      let lnode = [ IOne, ITwo ] `indexEx` j
      rnode <- go $ m - 1
      pure $ nodef lnode rnode

buildPostfixOpTree :: Int -> State StdGen PostTerm
buildPostfixOpTree n = i2po <$> buildInfixOpTree n

buildPrefixOpTree :: Int -> State StdGen PrefTerm
buildPrefixOpTree n = i2pr <$> buildInfixOpTree n

testCaseNumbers :: [Int]
testCaseNumbers = [100, 250, 500, 1500]

infixOpTreeCases :: [(String, ITerm)]
infixOpTreeCases =
  [ (show n, evalRandomState 0 $ buildInfixOpTree $ 2 * n + 1)
  | n <- testCaseNumbers
  ]

postfixOpTreeCases :: [(String, PostTerm)]
postfixOpTreeCases = do
  n <- testCaseNumbers
  let case1 = ("random-" <> show n, evalRandomState 0 $ buildPostfixOpTree $ 2 * n + 1)
  [ case1 ]

prefixOpTreeCases :: [(String, PrefTerm)]
prefixOpTreeCases = do
  n <- testCaseNumbers
  let case1 = ("random-" <> show n, evalRandomState 0 $ buildPrefixOpTree $ 2 * n + 1)
  [ case1 ]

benchSpec :: ([Benchmark], [NameableWeigh])
benchSpec = unzip
  [ nmGroup "i2po-rev"
    [ nmGroup "normal" $ testCases infixOpTreeCases $ i2po >>> reversePop
    , nmGroup "fusion" $ testCases infixOpTreeCases i2poRev
    , nmGroup "fusionOrig" $ testCases infixOpTreeCases i2poRevOrig
    ]
  , nmGroup "po2i-depth"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ po2i >>> depthRightSide
    , nmGroup "fusion" $ testCases postfixOpTreeCases po2iDepth
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases po2iDepthOrig
    ]
  , nmGroup "po2i-flat"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ po2i >>> flatRightSide
    , nmGroup "fusion" $ testCases postfixOpTreeCases po2iFlat
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases po2iFlatOrig
    ]
  {-, nmGroup "po2i-twoCounter"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ po2i >>> twoCounter
    , nmGroup "fusion" $ testCases postfixOpTreeCases po2iTwocounter
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases po2iTwocounterOrig
    ]-}
  , nmGroup "pr2i-i2pr"
    [ nmGroup "normal" $ testCases prefixOpTreeCases $ pr2i >>> i2pr
    , nmGroup "fusion" $ testCases prefixOpTreeCases pr2iI2pr
    , nmGroup "fusionOrig" $ testCases prefixOpTreeCases pr2iI2prOrig
    ]
  , nmGroup "po2i-i2pr"
    [ nmGroup "normal" $ testCases postfixOpTreeCases $ po2i >>> i2pr
    , nmGroup "fusion" $ testCases postfixOpTreeCases po2iI2pr
    , nmGroup "fusionOrig" $ testCases postfixOpTreeCases po2iI2prOrig
    ]
  ]
