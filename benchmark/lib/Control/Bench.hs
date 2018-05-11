module Control.Bench where

import           SmttPrelude

import           Criterion
import           Weigh


class Nameable a where
  type NameableElement a :: *

  nmGroup :: String -> [a] -> a
  nmItem :: String -> NameableElement a -> a


instance Nameable Benchmark where
  type NameableElement Benchmark = Benchmarkable

  nmGroup = bgroup
  nmItem = bench


newtype NameableWeigh = NameableWeigh (Maybe String -> Weigh ())

unNameWeigh :: NameableWeigh -> Weigh ()
unNameWeigh (NameableWeigh f) = f Nothing

nameableWeighFunc :: NFData a => (b -> a) -> b -> String -> Weigh ()
nameableWeighFunc f x s = func s f x

instance Nameable NameableWeigh where
  type NameableElement NameableWeigh = String -> Weigh ()

  nmGroup s ws = NameableWeigh $ \ms ->
    let
      ps = case ms of
        Nothing -> s
        Just s' -> s' <> "/" <> s
    in traverse_ (\(NameableWeigh f) -> f $ Just ps) ws

  nmItem s f = NameableWeigh $ \ms ->
    let
      ps = case ms of
        Nothing -> s
        Just s' -> s' <> "/" <> s
    in f ps


instance (Nameable a, Nameable b) => Nameable (a, b) where
  type NameableElement (a, b) = (NameableElement a, NameableElement b)

  nmGroup s = bimap (nmGroup s) (nmGroup s) . unzip

  nmItem s = bimap (nmItem s) (nmItem s)
