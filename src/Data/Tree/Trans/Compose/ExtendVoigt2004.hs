module Data.Tree.Trans.Compose.ExtendVoigt2004 where

import           SattPrelude

import           Data.Tree.RankedTree
import qualified Data.Tree.Trans.ATT                as ATT
import           Data.Tree.Trans.Compose.Desc       (ComposedAttInhAttr (..),
                                                     ComposedAttSynAttr (..),
                                                     composeAtts)
import           Data.Tree.Trans.Decompose.MttToAtt (decomposeMtt)
import qualified Data.Tree.Trans.MAC                as MAC
import qualified Data.Tree.Trans.TOP                as TOP
import qualified Data.Tree.Trans.SATT as SATT
import qualified Data.Tree.Trans.SMAC as SMAC
import Data.Tree.Trans.Compose.TdttAndSmtt (composeTdttAndSmtt, ComposedSmttState (..))

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
  pure $ fromMaybe errorUnreachable $ composeAtts trans1' trans2


composeTdttAndSatt ::
  ( TOP.TdttConstraint s ti1 li1 to1 lo1
  , to1 ~ ti2
  , SATT.SattConstraint syn inh ti2 li2 to2 lo2
  )
  => TOP.TopDownTreeTransducer s ti1 li1 to1 lo1
  -> SATT.StackAttributedTreeTransducer syn inh ti2 li2 to2 lo2
  -> SMAC.StackMacroTreeTransducer (ComposedSmttState s (SATT.SmttStateFromSatt syn)) ti1 li1 to2 lo2
composeTdttAndSatt trans1 trans2 = composeTdttAndSmtt trans1
  $ SATT.toStackMacroTreeTransducer trans2
