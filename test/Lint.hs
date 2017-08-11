module Main where

import Control.Monad
import Data.Semigroup
import Language.Haskell.HLint
import System.Environment
import System.Exit

main :: IO ()
main = do
  args <- getArgs
  hints <- hlint $ ["Setup.hs", "src", "test", "benchmark", "app"] <> args
  unless (null hints) exitFailure
