module Main where

import           SmttPrelude

import           Criterion.Main
import           Fusion         (benchSpec)


main :: IO ()
main = defaultMain criterionTasks
  where
    (criterionTasks, _) = benchSpec
