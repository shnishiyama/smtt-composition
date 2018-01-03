module Data.Tree.Trans.Compose.ExtendDesc where

import           SattPrelude

import qualified Data.Tree.Trans.SATT as SATT


data ComposedSattSynAttr syn1 inh1 syn2 inh2
  = SynSynAttr syn1 syn2
  | InhInhAttr inh1 inh2
  deriving (Eq, Ord, Show, Generic)

instance (Hashable syn1, Hashable inh1, Hashable syn2, Hashable inh2)
  => Hashable (ComposedSattSynAttr syn1 inh1 syn2 inh2)

data ComposedSattInhAttr syn1 inh1 syn2 inh2
  = SynInhAttr syn1 inh2
  | InhSynAttr inh1 syn2
  deriving (Eq, Ord, Show, Generic)

instance (Hashable syn1, Hashable inh1, Hashable syn2, Hashable inh2)
  => Hashable (ComposedSattInhAttr syn1 inh1 syn2 inh2)

type ComposedSattRHS syn1 inh1 syn2 inh2 t l = SATT.RightHandSide
  (ComposedSattSynAttr syn1 inh1 syn2 inh2)
  (ComposedSattInhAttr syn1 inh1 syn2 inh2)
  t l
