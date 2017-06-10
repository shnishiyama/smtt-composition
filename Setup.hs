{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

#ifndef MIN_VERSION_cabal_doctest
#define MIN_VERSION_cabal_doctest(x,y,z) 0
#endif

#if MIN_VERSION_cabal_doctest(1,0,0)

import Distribution.Simple
import Distribution.Extra.Doctest ( generateBuildModule )

main :: IO ()
main = defaultMainWithHooks simpleUserHooks
  { buildHook = buildHookScript
  }
  where
    buildHookScript pkg lbi hooks flags = do
      generateBuildModule "doc-test" flags pkg lbi -- generate Build_doctests
      buildHook simpleUserHooks pkg lbi hooks flags

#elif MIN_VERSION_Cabal(1,24,0)
  {-# WARNING ["You are configuring this package withou
t cabal-doctest installed.",
               "The doctests test-suite will not work a
s a result.",
               "To fix this, install cabal-doctest befo
re configuring."] #-}

main :: IO ()
main = defaultMain

#else

-- does not supported

#endif
