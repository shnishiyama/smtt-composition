module Main where

import SattPrelude

import Weigh
import Fusion (benchSpec)
import Control.Bench


main :: IO ()
main = mainWith $ traverse_ unNameWeigh weighTasks
  where
    (_, weighTasks) = benchSpec
