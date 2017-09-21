{-# LANGUAGE OverloadedStrings #-}

module Main where

import           ClassyPrelude
import           Control.DeepSeq

import Data.Tree.RankedTree.Instances
import Data.Tree.Trans.Class
import Data.Tree.Trans.ATT.Instances
import Data.Tree.Trans.ATT.Compose

mkInfixOpTreeSample :: Int -> InfixOpTree
mkInfixOpTreeSample 1 = InfixOne
mkInfixOpTreeSample 2 = InfixPlus InfixOne InfixTwo
mkInfixOpTreeSample n = InfixMulti (mkInfixOpTreeSample (n `div` 3)) (mkInfixOpTreeSample (n - (n `div` 3)))

main :: IO ()
main = do
  let treeSample = mkInfixOpTreeSample 10
  print $ treeTrans identityTransducer . treeTrans infixToPostfixTransducer $ treeSample
