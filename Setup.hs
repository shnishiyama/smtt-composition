{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE CPP               #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main where

import SattPrelude

#ifndef MIN_VERSION_cabal_doctest
#define MIN_VERSION_cabal_doctest(x,y,z) 0
#endif

#if MIN_VERSION_cabal_doctest(1,0,0)

import Distribution.Simple
import Distribution.Extra.Doctest ( addDoctestsUserHook )

main :: IO ()
main = defaultMainWithHooks
  $ addDoctestsUserHook "doc-test" simpleUserHooks

#else

  {-# WARNING
    [ "You are configuring this package without cabal-doctest installed."
    , "The doctests test-suite will not work as a result."
    , "To fix this, install cabal-doctest before configuring."
    ] #-}

main :: IO ()
main = defaultMain

#endif
