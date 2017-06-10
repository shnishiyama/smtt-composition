module Data.SATT.SATT where

import Data.SATT.ATT

-- | Stack-Attributed Tree Transducer
data StackAttrTreeTrans syn inh ta tb = StackAttrTreeTrans
  { initialAttr     :: syn
  , synthesizedRule :: SynthesizedRuleType syn inh ta tb
  , inheritedRule   :: InheritedRuleType syn inh ta tb
  }
