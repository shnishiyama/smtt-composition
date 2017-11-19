module Main where

import           ClassyPrelude

import           Language.Haskell.HLint
import           System.Environment     as Env
import           System.Exit

targetPaths :: [String]
targetPaths = ["Setup.hs", "src", "test", "benchmark", "app"]

main :: IO ()
main = do
  args <- Env.getArgs
  hints <- hlint $ targetPaths <> args
  unless (null hints) exitFailure
