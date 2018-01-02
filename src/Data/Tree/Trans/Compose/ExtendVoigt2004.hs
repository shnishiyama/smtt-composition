module Data.Tree.Trans.Compose.ExtendVoigt2004 where

import SattPrelude

import Data.Tree.RankedTree
import qualified Data.Tree.Trans.TOP as TOP
import qualified Data.Tree.Trans.MAC as MAC
import qualified Data.Tree.Trans.ATT as ATT
import Data.Tree.Trans.Compose.Desc (composeAtts, ComposedAttSynAttr(..), ComposedAttInhAttr(..))
import Data.Tree.Trans.Decompose.MttToAtt (decomposeMtt)

-- FIXME: give the implementation
checkWeaklySingleUse :: MonadThrow m => MAC.MacroTreeTransducer s ta la tb lb -> m ()
checkWeaklySingleUse _ = pure ()

type AttFromMttwsu s ta la tb lb = ATT.AttributedTreeTransducer
  (ComposedAttSynAttr s Void () RankNumber)
  (ComposedAttInhAttr s Void () RankNumber)
  ta la tb lb

-- | From weakly single-use mtts
--
-- Examples:
-- >>> import Data.Tree.RankedTree.Label
-- >>> import Data.Tree.Trans.MAC.Instances
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> trans <- fromMttwsuToAtt sampleMtt
-- >>> treeTrans trans inputSampleTree
-- D(F,F)
-- >>> (==) <$> (treeTrans trans $ inputSampleTree) <*> treeTrans sampleMtt inputSampleTree
-- True
--
fromMttwsuToAtt ::
  ( MAC.MttConstraint s ta la tb lb
  , Eq lb, Hashable lb
  , MonadThrow m
  )
  => MAC.MacroTreeTransducer s ta la tb lb
  -> m (AttFromMttwsu s ta la tb lb)
fromMttwsuToAtt trans = do
  checkWeaklySingleUse trans
  let (trans1, trans2) = decomposeMtt trans
  let trans1' = TOP.toAttributedTreeTransducer trans1
  pure $ fromMaybe (error "unreachable") $ composeAtts trans1' trans2
