module Language.Haskell.Encoding where

import           SattPrelude

import qualified Data.Char   as Char

showHexWithMaxNumber :: Integral i => i -> i -> String
showHexWithMaxNumber = showHexWithWidth . width (16 :: Int)
  where
    width n m = goWidth n m 1

    goWidth n m i = let m' = m `div` 16 in if
      | m' == 0   -> i
      | otherwise -> goWidth n m' $ i + 1

showHexWithWidth :: Integral i => Int -> i -> String
showHexWithWidth = go ""
  where
    go s 0 _ = s
    go s w i = go (showHexChar (i `mod` 16):s) (w - 1) (i `div` 16)

    showHexChar  0 = '0'
    showHexChar  1 = '1'
    showHexChar  2 = '2'
    showHexChar  3 = '3'
    showHexChar  4 = '4'
    showHexChar  5 = '5'
    showHexChar  6 = '6'
    showHexChar  7 = '7'
    showHexChar  8 = '8'
    showHexChar  9 = '9'
    showHexChar 10 = 'a'
    showHexChar 11 = 'b'
    showHexChar 12 = 'c'
    showHexChar 13 = 'd'
    showHexChar 14 = 'e'
    showHexChar 15 = 'f'
    showHexChar _  = errorUnreachable

encodeToIdentifier :: String -> String -> String
encodeToIdentifier s x = "i_" <> go x
  where
    go [] = '_':s
    go (c:cs)
      | isVarid c = c:go cs
      | otherwise = '_':go cs

    isVarid c = Char.isAlphaNum c || c == '\'' || c == '_'

