module Main where

import Build_doctests (flags, pkgs, module_sources)
import Data.Foldable (traverse_)
import Test.DocTest

main :: IO ()
main = do
  let args = flags ++ pkgs ++ module_sources

  traverse_ putStrLn args
  doctest args
