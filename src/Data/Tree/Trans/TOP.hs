{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.TOP
  ( -- common
    TopDownTreeTransducer
  , TdttTransducer
  , TdttConstraint
  , buildTdtt
  , RightHandSide
  , pattern TdttState
  , tdttState
  , pattern TdttLabelSide
  , MAC.prettyShowRhs

    -- bottom
  , MAC.bottomLabelSide

    -- conversion
  , toMacroTreeTransducer
  , toAttributedTreeTransducer

    -- reduction system
  , ReductionState
  , buildTdttReduction
  , runTdttReduction
  , runTdttReductionWithHistory
  , toInitialReductionState
  , fromReductionState
  , MAC.prettyShowReductionState
  ) where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import           Data.Tree.RankedTree.Zipper
import qualified Data.Tree.Trans.ATT         as ATT
import           Data.Tree.Trans.Class
import qualified Data.Tree.Trans.MAC         as MAC


type TdttState s = ConstRankedLabel 1 s

type RightHandSide s tb lb = MAC.RightHandSide (TdttState s) tb lb

pattern TdttState :: s -> RankNumber -> RightHandSide s t l
pattern TdttState s u <- MAC.MttState (ConstRankedLabelWrapper s) u []

tdttState :: s -> RankNumber -> RightHandSide s t l
tdttState s u = MAC.MttState (ConstRankedLabelWrapper s) u []

pattern TdttLabelSide :: l -> NodeVec (RightHandSide s t l) -> RightHandSide s t l
pattern TdttLabelSide l cs = MAC.MttLabelSide l cs

{-# COMPLETE TdttState, TdttLabelSide #-}

newtype TopDownTreeTransducer s ta la tb lb = TopDownTreeTransducer
  { toMacroTreeTransducer :: MAC.MacroTreeTransducer (TdttState s) ta la tb lb
  } deriving (Eq, Generic)

instance (Show s, Show la, Show lb, TdttConstraint s ta la tb lb)
    => Show (TopDownTreeTransducer s ta la tb lb) where

  show (TopDownTreeTransducer trans) = "TopDownTreeTransducer {"
      <> " tdttStates = " <> show (toList $ MAC.mttStates trans) <> ","
      <> " tdttInitialExpr = " <> MAC.prettyShowRhs (MAC.mttInitialExpr trans) <> ","
      <> " tdttTransRules = [" <> intercalate ", " (showRule <$> mapToList (MAC.mttTransRules trans)) <> "],"
      <> " }"
    where
      showRule (k, rhs) = show k <> " -> " <> MAC.prettyShowRhs rhs

type TdttTransducer s ta tb
  = TopDownTreeTransducer s ta (LabelType ta) tb (LabelType tb)

type TdttConstraint s ta la tb lb =
  ( RtConstraint ta la
  , RtConstraint tb lb
  , Eq s, Hashable s
  , Eq la, Hashable la
  )

buildTdtt :: forall m s ta la tb lb. (TdttConstraint s ta la tb lb, MonadThrow m)
  => RightHandSide s tb lb -> [(s, la, RightHandSide s tb lb)]
  -> m (TopDownTreeTransducer s ta la tb lb)
buildTdtt ie rules = TopDownTreeTransducer <$> MAC.buildMtt ie (coerce rules)


-- reduction system

type ReductionState s ta la tb lb = MAC.ReductionState (TdttState s) ta la tb lb

buildTdttReduction :: forall tz b s ta la tb lb.
  ( TdttConstraint s ta la tb lb, RankedTreeZipper tz
  )
  => (RtApply tz (ReductionState s ta la tb lb) -> b -> b)
  -> b
  -> TopDownTreeTransducer s ta la tb lb
  -> ReductionState s ta la tb lb
  -> b
buildTdttReduction f is (TopDownTreeTransducer trans)
  = MAC.buildMttReduction f is trans

runTdttReduction :: forall s ta la tb lb. (TdttConstraint s ta la tb lb)
  => TopDownTreeTransducer s ta la tb lb
  -> ReductionState s ta la tb lb -> ReductionState s ta la tb lb
runTdttReduction (TopDownTreeTransducer trans) = MAC.runMttReduction trans

runTdttReductionWithHistory :: forall s ta la tb lb. (TdttConstraint s ta la tb lb)
  => TopDownTreeTransducer s ta la tb lb
  -> ReductionState s ta la tb lb -> [ReductionState s ta la tb lb]
runTdttReductionWithHistory (TopDownTreeTransducer trans) = MAC.runMttReductionWithHistory trans

toInitialReductionState :: TdttConstraint s ta la tb lb => TopDownTreeTransducer s ta la tb lb -> ta -> ReductionState s ta la tb lb
toInitialReductionState (TopDownTreeTransducer trans) = MAC.toInitialReductionState trans

fromReductionState :: TdttConstraint s ta la tb lb => ReductionState s ta la tb lb -> Maybe tb
fromReductionState = MAC.fromReductionState


-- A tree transduction for tdtts
instance TdttConstraint s ta la tb lb => TreeTransducer (TopDownTreeTransducer s ta la tb lb) ta tb where
  treeTrans trans
    =   toInitialReductionState trans
    >>> runTdttReduction trans
    >>> fromReductionState
    >>> maybe (throwErrorM "This tree transducer is illegal.") pure


toAttributedTreeTransducer :: TdttConstraint s ta la tb lb
  => TopDownTreeTransducer s ta la tb lb -> ATT.AttributedTreeTransducer s Void ta la tb lb
toAttributedTreeTransducer (TopDownTreeTransducer trans) = fromMaybe (error "unreachable") $ ATT.buildAtt
    (coerce $ headEx $ MAC.mttStates trans)
    [ (ATT.Synthesized (), replaceRHS $ MAC.mttInitialExpr trans)
    ]
    [ (ATT.Synthesized $ coerce s, l, replaceRHS rhs)
    | ((s, l), rhs) <- mapToList $ MAC.mttTransRules trans
    ]
  where
    replaceRHS (TdttState s u)      = ATT.AttAttrSide (ATT.Synthesized (s, u))
    replaceRHS (TdttLabelSide l cs) = ATT.AttLabelSide l $ replaceRHS <$> cs
