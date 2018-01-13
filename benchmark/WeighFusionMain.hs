module Main where

import           SattPrelude

import           Control.Bench
import           Fusion        (benchSpec)
import           Weigh


main :: IO ()
main = mainWith $ traverse_ unNameWeigh weighTasks
  where
    (_, weighTasks) = benchSpec
