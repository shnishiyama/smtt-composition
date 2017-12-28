module Main where

import           ClassyPrelude

import           Language.Haskell.HLint
import           System.Environment     as Env
import           System.Exit

targetPaths :: [String]
targetPaths = ["Setup.hs", "src", "test"]

hintPath :: [String]
hintPath = ["--hint=../HLint.hs"]

main :: IO ()
main = do
  args <- Env.getArgs
  hints <- hlint $ hintPath <> targetPaths <> args
  unless (null hints) exitFailure
