module Main where

import           SattPrelude

import           Build_doctests (flags, module_sources, pkgs)
import           Test.DocTest

customFlags :: [String]
customFlags = ["-fno-warn-warnings-deprecations", "-with-rtsopts=M1G"]

main :: IO ()
main = do
  let args = flags ++ customFlags ++ pkgs ++ module_sources
  doctest args
