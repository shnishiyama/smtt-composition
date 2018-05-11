module Main where

import           SmttPrelude

import           Control.Bench
import           Fusion        (benchSpec)
import           Weigh


main :: IO ()
main = mainWith $ traverse_ unNameWeigh weighTasks
  where
    (_, weighTasks) = benchSpec
