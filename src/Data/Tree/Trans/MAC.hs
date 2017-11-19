module Data.Tree.Trans.MAC where

-- | The class of macro tree transducers
class (RankedTree ta, RankedTree tb, TreeTransducer t) => MacroTreeTransducer t ta tb | t -> ta, t -> tb where
  reductionRule :: t
