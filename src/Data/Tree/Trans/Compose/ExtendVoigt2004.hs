module Data.Tree.Trans.Compose.ExtendVoigt2004 where

import           SmttPrelude

import           Data.Tree.RankedTree
import qualified Data.Tree.Trans.ATT                  as ATT
import           Data.Tree.Trans.Compose.Desc         (ComposedAttInhAttr,
                                                       ComposedAttSynAttr,
                                                       composeAtts)
import           Data.Tree.Trans.Compose.ExtendDesc   (ComposedSattSynAttr,
                                                       composeSattAndAtt)
import           Data.Tree.Trans.Compose.TdttAndSmtt  (composeTdttAndSmtt)
import qualified Data.Tree.Trans.Compose.TdttAndSmtt  as SMAC
import           Data.Tree.Trans.Decompose.MttToAtt   (decomposeMtt)
import           Data.Tree.Trans.Decompose.SmttToSatt (decomposeSmttNC)
import qualified Data.Tree.Trans.MAC                  as MAC
import qualified Data.Tree.Trans.SATT                 as SATT
import qualified Data.Tree.Trans.SMAC                 as SMAC
import qualified Data.Tree.Trans.TOP                  as TOP

-- FIXME: give the implementation
checkWeaklySingleUse :: MonadThrow m => MAC.MacroTreeTransducer s ta la tb lb -> m ()
checkWeaklySingleUse _ = pure ()

type AttFromMttWSU s ta la tb lb = ATT.AttributedTreeTransducer
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
-- >>> trans <- fromMttWSUToAtt sampleMtt
-- >>> treeTrans trans inputSampleTree
-- D(F,F)
-- >>> :{
-- flip runKleisli inputSampleTree $ proc t -> do
--   t1 <- Kleisli (treeTrans trans) -< t
--   t2 <- Kleisli (treeTrans sampleMtt) -< t
--   returnA -< t1 == t2
-- :}
-- True
--
fromMttWSUToAtt ::
  ( MAC.MttConstraint s ta la tb lb
  , Eq lb, Hashable lb
  , MonadThrow m
  )
  => MAC.MacroTreeTransducer s ta la tb lb
  -> m (AttFromMttWSU s ta la tb lb)
fromMttWSUToAtt trans = do
  checkWeaklySingleUse trans
  let (trans1, trans2) = decomposeMtt trans
  let trans1' = TOP.toAttributedTreeTransducer trans1
  pure $ fromMaybe errorUnreachable $ composeAtts trans1' trans2


-- | composition of a tdtt and a satt
--
-- Examples:
-- >>> import Data.Tree.RankedTree.Label
-- >>> import Data.Tree.RankedTree.Instances
-- >>> import Data.Tree.Trans.TOP.Instances
-- >>> import Data.Tree.Trans.SATT.Instances
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> traUniverse = setFromList $ taggedRankedAlphabetUniverse Proxy
-- >>> identInputTrans = identityTransducer @InputSampleTree traUniverse
-- >>> identSampleSmtt = composeTdttAndSatt identInputTrans sampleSatt
-- >>> treeTrans identSampleSmtt inputSampleTree
-- D(F,F)
-- >>> :{
-- flip runKleisli inputSampleTree $ proc t -> do
--   t1 <- Kleisli (treeTrans sampleSatt <=< treeTrans identInputTrans) -< t
--   t2 <- Kleisli (treeTrans identSampleSmtt) -< t
--   returnA -< t1 == t2
-- :}
-- True
--
composeTdttAndSatt ::
  ( TOP.TdttConstraint s ti1 li1 to1 lo1
  , to1 ~ ti2
  , SATT.SattConstraint syn inh ti2 li2 to2 lo2
  , Eq lo2, Hashable lo2
  , Show lo2, Show syn, Show s, Show lo1, Show li1
  )
  => TOP.TopDownTreeTransducer s ti1 li1 to1 lo1
  -> SATT.StackAttributedTreeTransducer syn inh ti2 li2 to2 lo2
  -> SMAC.StackMacroTreeTransducer (SMAC.ComposedSmttState s (SATT.SmttStateFromSatt syn)) ti1 li1 to2 lo2
composeTdttAndSatt trans1 trans2 = composeTdttAndSmtt trans1
  $ SATT.toStackMacroTreeTransducer trans2


type ComposedSmttState s1 s2 = SMAC.ComposedSmttState s1
  (SATT.SmttStateFromSatt
    (ComposedSattSynAttr () RankNumber
      (ComposedAttSynAttr s2 Void () RankNumber)
      (ComposedAttInhAttr s2 Void () RankNumber)
    )
  )

-- | composition of a nc-smtt and wsu-mtt
--
-- Examples:
-- >>> import Data.Tree.RankedTree.Label
-- >>> import Data.Tree.Trans.MAC.Instances
-- >>> import Data.Tree.Trans.SMAC.Instances
-- >>> import Data.Tree.Trans.Class
-- >>> pOne   = taggedRankedLabel @"one"
-- >>> pTwo   = taggedRankedLabel @"two"
-- >>> pPlus  = taggedRankedLabel @"plus"
-- >>> pMulti = taggedRankedLabel @"multi"
-- >>> pEnd   = taggedRankedLabel @"end"
-- >>> :{
-- inputPostfixTree = mkTree pTwo [mkTree pOne [mkTree pTwo
--   [mkTree pPlus [mkTree pMulti [mkTree pEnd []]]]
--   ]]
-- :}
--
-- >>> ptoiCounterTrans <- composeSmttNCAndMttWSU postfixToInfixSmtt twoCounterMtt
-- >>> treeTrans ptoiCounterTrans inputPostfixTree
-- Succ (Succ Zero)
-- >>> :{
-- flip runKleisli inputPostfixTree $ proc t -> do
--   t1 <- Kleisli (treeTrans ptoiCounterTrans) -< t
--   t2 <- Kleisli (treeTrans postfixToInfixSmtt >=> treeTrans twoCounterMtt) -< t
--   returnA -< t1 == t2
-- :}
-- True
--
-- >>> :{
-- inputNumTree = mkTree True [mkTree True [mkTree True
--   [mkTree True [mkTree False []]]
--   ]]
-- :}
--
-- skip:>>> expItopTrans <- composeSmttNCAndMttWSU sampleExpSmtt infixToPostfixMtt
-- skip:>>> treeTrans expItopTrans inputNumTree
--
-- skip:>>> :{
-- flip runKleisli inputNumTree $ proc t -> do
--   t1 <- Kleisli (treeTrans expItopTrans) -< t
--   t2 <- Kleisli (treeTrans sampleExpSmtt >=> treeTrans infixToPostfixMtt) -< t
--   returnA -< t1 == t2
-- :}
-- True
--
composeSmttNCAndMttWSU ::
  ( SMAC.SmttConstraint s1 ti1 li1 to1 lo1
  , to1 ~ ti2
  , MAC.MttConstraint s2 ti2 li2 to2 lo2
  , Eq lo2, Hashable lo2
  , MonadThrow m
  , Show lo2, Show s2, Show s1, Show lo1, Show li1
  )
  => SMAC.StackMacroTreeTransducer s1 ti1 li1 to1 lo1
  -> MAC.MacroTreeTransducer s2 ti2 li2 to2 lo2
  -> m (SMAC.StackMacroTreeTransducer (ComposedSmttState s1 s2) ti1 li1 to2 lo2)
composeSmttNCAndMttWSU trans1 trans2 = do
    (preTdtt, trans1Satt) <- decomposeSmttNC trans1
    trans2Att <- fromMttWSUToAtt trans2
    postSatt <- composeSattAndAtt trans1Satt trans2Att
    let composedTrans = composeTdttAndSatt preTdtt postSatt
    pure $ SMAC.toFormattedSmtt composedTrans
