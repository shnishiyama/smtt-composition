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

itopReverseCases :: [(String, InfixOpTree)]
itopReverseCases = [ (show n, evalRandomState 0 $ buildTree $ n + 1) | n <- [20, 50, 100] ]
  where
    buildTree 1 = do
      i <- nextRandomState
      pure $ [ InfixOneNode, InfixTwoNode ] `indexEx` (i `mod` 2)
    buildTree n = do
      i <- nextRandomState
      let nodef = [ InfixMultiNode, InfixPlusNode ] `indexEx` (i `mod` 2)
      let n2 = n `div` 2
      m <- nextRandomState
      let m' = 2 * (m `mod` n2) + 1
      lnode <- buildTree m'
      rnode <- buildTree $ n - m' - 1
      pure $ nodef lnode rnode


benchSpec :: ([Benchmark], [NameableWeigh])
benchSpec = unzip
  [ nmGroup "itop-reverse"
    [ nmGroup "normal" $ testCases itopReverseCases $ reversePop . itop
    , nmGroup "fusion" $ testCases itopReverseCases itopReversePop
    , nmGroup "fusionOrig" $ testCases itopReverseCases itopReversePopOrig
    ]
  ]
