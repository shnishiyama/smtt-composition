module Main where

import Build_doctests (flags, pkgs, module_sources)
import Test.DocTest

main :: IO ()
main = do
  let customflags = ["-fno-warn-warnings-deprecations"]
  let args = flags ++ customflags ++ pkgs ++ module_sources

  doctest args
