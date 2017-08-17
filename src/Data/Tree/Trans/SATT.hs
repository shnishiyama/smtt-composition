{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE TypeInType        #-}

module Data.Tree.Trans.SATT
  (
    -- satt attribute tags
    SattAttrTag
  , OutAttrTag
  , StkAttrTag
  , TaggedOut
  , TaggedStk
  , SattAttrEither
  , taggedOut
  , taggedStk
  , pattern TaggedOut
  , pattern TaggedStk
  , SattAttrEitherBox
  , taggedOutBox
  , taggedStkBox
  , pattern TaggedOutBox
  , pattern TaggedStkBox

    -- common
  , InputLabelType
  , InputRankedTree
  , InputRankedTreeZipper
  , OutRightHandSide
  , StkRightHandSide
  , RightHandSide(..)
  , RightHandSideBox(..)
  , AttrSide
  , synAttrSide
  , inhAttrSide
  , stsynAttrSide
  , stinhAttrSide
  , TreeOutRightHandSide
  , TreeStkRightHandSide
  , TreeRightHandSide
  , TreeRightHandSideBox
  , InputOutAttr
  , InputStkAttr
  , InputAttr
  , pattern SynAttr
  , pattern InhAttr
  , pattern StSynAttr
  , pattern StInhAttr
  , toInputAttr
  , SattRuleType
  , StackAttrTreeTrans(..)

    -- reduction state
  , ReductionAttrState(..)
  , ReductionOutAttrState
  , ReductionStkAttrState
  , toReductionAttrState
  , initialSattReductionState
  , ReductionState(..)
  , TreeReductionOutState
  , TreeReductionStkState
  , ReductionStateBox(..)
  , TreeReductionStateBox
  , fromTreeReductionState
  , ReductionStateLabel(..)
  , ReductionStateLabelBox(..)
  , TreeReductionStateLabelBox
  , reductionStateLabelBox
  , TreeReductionStateZipper

    -- reduction system
  , buildSattReduction
  , runSattReduction
  , ReductionStep(..)
  , TreeReductionStep
  , ReductionStateStep(..)
  , ReductionSteps(..)
  , TreeReductionSteps
  , buildSattReductionSteps
  , buildSattReductionSteps'

    -- bottom label
  , bottomLabelSide
  ) where

import           ClassyPrelude

import           Control.Arrow               hiding (first, second)
import           Data.Pattern.Error
import           Data.Profunctor.Unsafe
import           Data.TypeLevel.TaggedEither

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Zipper
import           Data.Tree.Trans.ATT         (AttAttrEitherBox, InhAttrTag,
                                              SynAttrTag, pattern TaggedInhBox,
                                              pattern TaggedSynBox,
                                              taggedInhBox, taggedSynBox)
import qualified Data.Tree.Trans.ATT         as ATT
import           Data.Tree.Trans.Class

-- attibute kinds

type SattAttrTag = EitherTag

type OutAttrTag = 'LeftTag
type StkAttrTag = 'RightTag

type TaggedOut = SattAttrEither OutAttrTag
type TaggedStk = SattAttrEither StkAttrTag

type SattAttrEither = TaggedEither
type SattAttrEitherBox = TaggedEitherBox

taggedOut :: out -> TaggedOut out stk
taggedOut = TaggedLeft

taggedStk :: stk -> TaggedStk out stk
taggedStk = TaggedRight

taggedOutBox :: out -> SattAttrEitherBox out stk
taggedOutBox = taggedLeftBox

taggedStkBox :: stk -> SattAttrEitherBox out stk
taggedStkBox = taggedRightBox

pattern TaggedOut
  :: () => tag ~ SynAttrTag
  => out -> SattAttrEither tag out stk
pattern TaggedOut x = TaggedLeft x

pattern TaggedStk
  :: () => tag ~ InhAttrTag
  => stk -> SattAttrEither tag out stk
pattern TaggedStk x = TaggedRight x

pattern TaggedOutBox :: out -> SattAttrEitherBox out stk
pattern TaggedOutBox x = TaggedLeftBox x

pattern TaggedStkBox :: stk -> SattAttrEitherBox out stk
pattern TaggedStkBox x = TaggedRightBox x

-- common

type RTZipperWithInitial tz t l = tz (RankedTreeWithInitial t l) (RankedTreeLabelWithInitial t l)

type InputLabelType t = RtApply RankedTreeLabelWithInitial t
type InputRankedTree t = RtApply RankedTreeWithInitial t
type InputRankedTreeZipper tz t = RTZipperWithInitial tz t (LabelType t)

type AttrSide tag syn inh stsyn stinh
  = SattAttrEither tag (ATT.AttrSide syn inh) (ATT.AttrSide stsyn stinh)

type OutRightHandSide = RightHandSide OutAttrTag
type StkRightHandSide = RightHandSide StkAttrTag

data RightHandSide (tag :: SattAttrTag) syn inh stsyn stinh t l where
  AttrSide       :: AttrSide tag syn inh stsyn stinh
    -> RightHandSide tag syn inh stsyn stinh t l
  LabelSide      :: l -> (NodeVec :$ OutRightHandSide syn inh stsyn stinh t l)
    -> OutRightHandSide syn inh stsyn stinh t l
  StackHeadSide  :: StkRightHandSide syn inh stsyn stinh t l
    -> OutRightHandSide syn inh stsyn stinh t l
  StackConsSide  :: OutRightHandSide syn inh stsyn stinh t l
    -> StkRightHandSide syn inh stsyn stinh t l
    -> StkRightHandSide syn inh stsyn stinh t l
  StackTailSide  :: StkRightHandSide syn inh stsyn stinh t l
    -> StkRightHandSide syn inh stsyn stinh t l
  StackEmptySide :: StkRightHandSide syn inh stsyn stinh t l

data RightHandSideBox syn inh stsyn stinh t l
  = forall tag. RightHandSideBox (RightHandSide tag syn inh stsyn stinh t l)

synAttrSide :: syn -> RankNumber -> OutRightHandSide syn inh stsyn stinh t l
synAttrSide a i = AttrSide . taggedOut $ taggedSynBox (a, i)

inhAttrSide :: inh -> OutRightHandSide syn inh stsyn stinh t l
inhAttrSide a = AttrSide . taggedOut $ TaggedInhBox a

stsynAttrSide :: stsyn -> RankNumber -> StkRightHandSide syn inh stsyn stinh t l
stsynAttrSide a i = AttrSide . taggedStk $ taggedSynBox (a, i)

stinhAttrSide :: stinh -> StkRightHandSide syn inh stsyn stinh t l
stinhAttrSide a = AttrSide . taggedStk $ TaggedInhBox a

type TreeOutRightHandSide syn inh stsyn stinh t = TreeRightHandSide OutAttrTag syn inh stsyn stinh t
type TreeStkRightHandSide syn inh stsyn stinh t = TreeRightHandSide StkAttrTag syn inh stsyn stinh t
type TreeRightHandSide tag syn inh stsyn stinh t = RtApply (RightHandSide tag syn inh stsyn stinh) t
type TreeRightHandSideBox syn inh stsyn stinh t = RtApply (RightHandSideBox syn inh stsyn stinh) t

type InputAttr tag syn inh stsyn stinh
  = SattAttrEither tag (ATT.InputAttr syn inh) (ATT.InputAttr stsyn stinh)

type InputOutAttr syn inh stsyn stinh
  = InputAttr OutAttrTag syn inh stsyn stinh
type InputStkAttr syn inh stsyn stinh
  = InputAttr StkAttrTag syn inh stsyn stinh

pattern SynAttr :: syn -> InputOutAttr syn inh stsyn stinh
pattern SynAttr a = TaggedOut (ATT.SynAttr a)

pattern InhAttr :: inh -> RankNumber -> InputOutAttr syn inh stsyn stinh
pattern InhAttr b i = TaggedOut (ATT.InhAttr b i)

pattern StSynAttr :: stsyn -> InputStkAttr syn inh stsyn stinh
pattern StSynAttr a = TaggedStk (ATT.SynAttr a)

pattern StInhAttr :: stinh -> RankNumber -> InputStkAttr syn inh stsyn stinh
pattern StInhAttr b i = TaggedStk (ATT.InhAttr b i)

toInputAttr
  :: SattAttrEither tag (AttAttrEitherBox syn inh) (AttAttrEitherBox stsyn stinh) -> [RankNumber]
  -> (InputAttr tag syn inh stsyn stinh, [RankNumber])
toInputAttr (TaggedOut a) = first TaggedOut . ATT.toInputAttr a
toInputAttr (TaggedStk a) = first TaggedStk . ATT.toInputAttr a
toInputAttr _             = unreachable

type SattRuleType tag syn inh stsyn stinh ta tb
  = InputAttr tag syn inh stsyn stinh -> InputLabelType ta
  -> TreeRightHandSide tag syn inh stsyn stinh tb

-- | Stack-Attributed Tree Transducer
data StackAttrTreeTrans syn inh stsyn stinh ta tb = StackAttrTreeTrans
  { initialAttr   :: syn
  , reductionRule :: forall tag. SattRuleType tag syn inh stsyn stinh ta tb
  }


-- reduction states

type ReductionOutAttrState = ReductionAttrState OutAttrTag
type ReductionStkAttrState  = ReductionAttrState StkAttrTag

data ReductionAttrState tag syn inh stsyn stinh = ReductionAttrState
  { reductionAttrState :: SattAttrEither tag
    (AttAttrEitherBox syn inh) (AttAttrEitherBox stsyn stinh)
  , reductionPathState :: [RankNumber]
  } deriving (Eq, Ord)

pattern ReductionOutAttrState :: () => tag ~ OutAttrTag
  => AttAttrEitherBox syn inh -> [RankNumber] -> ReductionAttrState tag syn inh stsyn stinh
pattern ReductionOutAttrState a p = ReductionAttrState (TaggedOut a) p

pattern ReductionStkAttrState :: () => tag ~ StkAttrTag
  => AttAttrEitherBox stsyn stinh -> [RankNumber] -> ReductionAttrState tag syn inh stsyn stinh
pattern ReductionStkAttrState a p = ReductionAttrState (TaggedStk a) p

instance (Show syn, Show inh, Show stsyn, Show stinh) => Show (ReductionAttrState tag syn inh stsyn stinh) where
  show (ReductionAttrState abox p) = case abox of
      TaggedOut attbox -> showAttAttrState attbox
      TaggedStk attbox -> showAttAttrState attbox
      _                -> unreachable
    where
      showAttAttrState (TaggedSynBox a) = showAttrState a
      showAttAttrState (TaggedInhBox a) = showAttrState a
      showAttAttrState _                = unreachable

      showAttrState :: Show a => a -> String
      showAttrState x = show x <> show (reverse p)


type ReductionOutState = ReductionState OutAttrTag
type ReductionStkState = ReductionState StkAttrTag

data ReductionState (tag :: SattAttrTag) tz syn inh stsyn stinh ta la tb lb where
  AttrState       :: RTZipperWithInitial tz ta la -> ReductionAttrState tag syn inh stsyn stinh
    -> ReductionState tag tz syn inh stsyn stinh ta la tb lb
  RankedTreeState :: lb -> (NodeVec :$ ReductionOutState tz syn inh stsyn stinh ta la tb lb)
    -> ReductionOutState tz syn inh stsyn stinh ta la tb lb
  StackHeadState  :: ReductionStkState tz syn inh stsyn stinh ta la tb lb
    -> ReductionOutState tz syn inh stsyn stinh ta la tb lb
  StackConsState  :: ReductionOutState tz syn inh stsyn stinh ta la tb lb
    -> ReductionStkState tz syn inh stsyn stinh ta la tb lb
    -> ReductionStkState tz syn inh stsyn stinh ta la tb lb
  StackTailState  :: ReductionStkState tz syn inh stsyn stinh ta la tb lb
    -> ReductionStkState tz syn inh stsyn stinh ta la tb lb
  StackEmptyState :: ReductionStkState tz syn inh stsyn stinh ta la tb lb

instance (Eq syn, Eq inh, Eq stsyn, Eq stinh, Eq lb, RtConstraint tb lb)
  => Eq (ReductionState tag tz syn inh stsyn stinh ta la tb lb) where
    t1 == t2 = ReductionStateBox t1 == ReductionStateBox t2

instance (Ord syn, Ord inh, Ord stsyn, Ord stinh, Ord lb, RtConstraint tb lb)
  => Ord (ReductionState tag tz syn inh stsyn stinh ta la tb lb) where
    t1 `compare` t2 = ReductionStateBox t1 `compare` ReductionStateBox t2

instance (Show syn, Show inh, Show stsyn, Show stinh, Show lb, RtConstraint tb lb)
  => Show (ReductionState tag tz syn inh stsyn stinh ta la tb lb) where
    show = show . ReductionStateBox

data ReductionStateBox tz syn inh stsyn stinh ta la tb lb = forall tag.
  ReductionStateBox (ReductionState tag tz syn inh stsyn stinh ta la tb lb)

reductionStateBox
  :: ReductionStateBox tz syn inh stsyn stinh ta la tb lb
  -> SattAttrEitherBox
    (ReductionOutState tz syn inh stsyn stinh ta la tb lb)
    (ReductionStkState tz syn inh stsyn stinh ta la tb lb)
reductionStateBox (ReductionStateBox x) = case x of
  AttrState _ (ReductionOutAttrState _ _) -> TaggedOutBox x
  AttrState _ (ReductionStkAttrState _ _) -> TaggedStkBox x
  AttrState _ _                           -> unreachable
  RankedTreeState _ _                     -> TaggedOutBox x
  StackHeadState _                        -> TaggedOutBox x
  StackConsState _ _                      -> TaggedStkBox x
  StackTailState _                        -> TaggedStkBox x
  StackEmptyState                         -> TaggedStkBox x

instance (Eq syn, Eq inh, Eq stsyn, Eq stinh, Eq lb, RtConstraint tb lb)
  => Eq (ReductionStateBox tz syn inh stsyn stinh ta la tb lb) where
    t1 == t2 = wrapRankedTree t1 == wrapRankedTree t2

instance (Ord syn, Ord inh, Ord stsyn, Ord stinh, Ord lb, RtConstraint tb lb)
  => Ord (ReductionStateBox tz syn inh stsyn stinh ta la tb lb) where
    t1 `compare` t2 = wrapRankedTree t1 `compare` wrapRankedTree t2

instance (Show syn, Show inh, Show stsyn, Show stinh, Show lb, RtConstraint tb lb)
  => Show (ReductionStateBox tz syn inh stsyn stinh ta la tb lb) where
    show = show .# wrapRankedTree

type TreeReductionOutState tz syn inh stsyn stinh ta tb = TreeReductionState OutAttrTag tz syn inh stsyn stinh ta tb
type TreeReductionStkState tz syn inh stsyn stinh ta tb = TreeReductionState StkAttrTag tz syn inh stsyn stinh ta tb
type TreeReductionState tag tz syn inh stsyn stinh ta tb
  = RtApply (RtApply (ReductionState tag tz syn inh stsyn stinh) ta) tb
type TreeReductionStateBox tz syn inh stsyn stinh ta tb
  = RtApply (RtApply (ReductionStateBox tz syn inh stsyn stinh) ta) tb

fromTreeReductionState :: RankedTree tb => TreeReductionState tag tz syn inh stsyn stinh ta tb -> Maybe tb
fromTreeReductionState (RankedTreeState l ss) = pure (mkTree l) <*> traverse fromTreeReductionState ss
fromTreeReductionState _                      = empty

initialSattReductionState :: StackAttrTreeTrans syn inh stsyn stinh ta tb -> ReductionOutAttrState syn inh stsyn stinh
initialSattReductionState StackAttrTreeTrans{ initialAttr = a0 }
  = ReductionAttrState (taggedOut (taggedSynBox a0)) []

toReductionAttrState :: AttrSide tag syn inh stsyn stinh -> [RankNumber] -> ReductionAttrState tag syn inh stsyn stinh
toReductionAttrState as p = case as of
    TaggedOut atts ->
      let (a, p') = toAttAttrState atts in ReductionAttrState (taggedOut a) p'
    TaggedStk atts ->
      let (a, p') = toAttAttrState atts in ReductionAttrState (taggedStk a) p'
    _              -> unreachable
  where
    toAttAttrState :: ATT.AttrSide s i -> (AttAttrEitherBox s i, [RankNumber])
    toAttAttrState (TaggedSynBox (a, i)) = (taggedSynBox a, i:p)
    toAttAttrState (TaggedInhBox a)      = (taggedInhBox a, p)
    toAttAttrState _                     = unreachable


type ReductionOutStateLabel = ReductionStateLabel OutAttrTag
type ReductionStkStateLabel = ReductionStateLabel StkAttrTag

data ReductionStateLabel (tag :: SattAttrTag) tz syn inh stsyn stinh ta la tb lb where
  AttrStateLabel       :: RTZipperWithInitial tz ta la -> ReductionAttrState tag syn inh stsyn stinh
    -> ReductionStateLabel tag tz syn inh stsyn stinh ta la tb lb
  RankedTreeStateLabel :: lb -> ReductionOutStateLabel tz syn inh stsyn stinh ta la tb lb
  StackHeadStateLabel  :: ReductionOutStateLabel tz syn inh stsyn stinh ta la tb lb
  StackConsStateLabel  :: ReductionStkStateLabel tz syn inh stsyn stinh ta la tb lb
  StackTailStateLabel  :: ReductionStkStateLabel tz syn inh stsyn stinh ta la tb lb
  StackEmptyStateLabel :: ReductionStkStateLabel tz syn inh stsyn stinh ta la tb lb

instance (Eq syn, Eq inh, Eq stsyn, Eq stinh, Eq lb)
  => Eq (ReductionStateLabel tag tz syn inh stsyn stinh ta la tb lb) where
    x == y = ReductionStateLabelBox x == ReductionStateLabelBox y

instance (Ord syn, Ord inh, Ord stsyn, Ord stinh, Ord lb)
  => Ord (ReductionStateLabel tag tz syn inh stsyn stinh ta la tb lb) where
    x `compare` y = ReductionStateLabelBox x `compare` ReductionStateLabelBox y

instance (Show syn, Show inh, Show stsyn, Show stinh, Show lb)
  => Show (ReductionStateLabel tag tz syn inh stsyn stinh ta la tb lb) where
    show (AttrStateLabel _ a)     = show a
    show (RankedTreeStateLabel l) = show l
    show StackEmptyStateLabel     = "Empty"
    show StackHeadStateLabel      = "Head"
    show StackConsStateLabel      = "Cons"
    show StackTailStateLabel      = "Tail"

data ReductionStateLabelBox tz syn inh stsyn stinh ta la tb lb = forall tag.
  ReductionStateLabelBox (ReductionStateLabel tag tz syn inh stsyn stinh ta la tb lb)

reductionStateLabelBox
  :: ReductionStateLabelBox tz syn inh stsyn stinh ta la tb lb
  -> SattAttrEitherBox
    (ReductionOutStateLabel tz syn inh stsyn stinh ta la tb lb)
    (ReductionStkStateLabel tz syn inh stsyn stinh ta la tb lb)
reductionStateLabelBox (ReductionStateLabelBox x) = case x of
  AttrStateLabel _ (ReductionOutAttrState _ _) -> TaggedOutBox x
  AttrStateLabel _ (ReductionStkAttrState _ _) -> TaggedStkBox x
  AttrStateLabel _ _                           -> unreachable
  RankedTreeStateLabel _                       -> TaggedOutBox x
  StackHeadStateLabel                          -> TaggedOutBox x
  StackConsStateLabel                          -> TaggedStkBox x
  StackTailStateLabel                          -> TaggedStkBox x
  StackEmptyStateLabel                         -> TaggedStkBox x

instance (Eq syn, Eq inh, Eq stsyn, Eq stinh, Eq lb)
  => Eq (ReductionStateLabelBox tz syn inh stsyn stinh ta la tb lb) where
    ReductionStateLabelBox x == ReductionStateLabelBox y = case (x, y) of
        (AttrStateLabel _ ax    , AttrStateLabel _ ay    ) -> ax `eqAttrState` ay
        (RankedTreeStateLabel lx, RankedTreeStateLabel ly) -> lx == ly
        (StackHeadStateLabel    , StackHeadStateLabel    ) -> True
        (StackConsStateLabel    , StackConsStateLabel    ) -> True
        (StackTailStateLabel    , StackTailStateLabel    ) -> True
        (StackEmptyStateLabel   , StackEmptyStateLabel   ) -> True
        _                                                  -> False
      where
        eqAttrState
          :: ReductionAttrState tag1 syn inh stsyn stinh
          -> ReductionAttrState tag2 syn inh stsyn stinh
          -> Bool
        eqAttrState ax ay = case (ax, ay) of
          (ReductionOutAttrState _ _, ReductionOutAttrState _ _) -> ax == ay
          (ReductionStkAttrState _ _, ReductionStkAttrState _ _) -> ax == ay
          _                                                      -> False


instance (Ord syn, Ord inh, Ord stsyn, Ord stinh, Ord lb)
  => Ord (ReductionStateLabelBox tz syn inh stsyn stinh ta la tb lb) where
    ReductionStateLabelBox x `compare` ReductionStateLabelBox y = case (x, y) of
        (AttrStateLabel _ ax    , AttrStateLabel _ ay    ) -> ax `compareAttrState` ay
        (RankedTreeStateLabel lx, RankedTreeStateLabel ly) -> lx `compare` ly
        _ -> stateLabelNum x `compare` stateLabelNum y
      where
        compareAttrState
          :: ReductionAttrState tag1 syn inh stsyn stinh
          -> ReductionAttrState tag2 syn inh stsyn stinh
          -> Ordering
        compareAttrState ax ay = case (ax, ay) of
          (ReductionOutAttrState _ _, ReductionOutAttrState _ _) -> ax `compare` ay
          (ReductionStkAttrState _ _, ReductionStkAttrState _ _) -> ax `compare` ay
          (ReductionOutAttrState _ _, _) -> LT
          _                              -> GT

        stateLabelNum :: ReductionStateLabel tag tz syn inh stsyn stinh ta la tb lb -> Int
        stateLabelNum (AttrStateLabel _ _)     = 0
        stateLabelNum (RankedTreeStateLabel _) = 1
        stateLabelNum StackHeadStateLabel      = 2
        stateLabelNum StackConsStateLabel      = 3
        stateLabelNum StackTailStateLabel      = 4
        stateLabelNum StackEmptyStateLabel     = 5

instance (Show syn, Show inh, Show stsyn, Show stinh, Show lb)
  => Show (ReductionStateLabelBox tz syn inh stsyn stinh ta la tb lb) where
    show (ReductionStateLabelBox x) = show x

type TreeReductionStateLabelBox tz syn inh stsyn stinh ta tb
  = RtApply (RtApply (ReductionStateLabelBox tz syn inh stsyn stinh) ta) tb

instance (RtConstraint tb lb)
  => RankedTree (ReductionStateBox tz syn inh stsyn stinh ta la tb lb) where

    type LabelType (ReductionStateBox tz syn inh stsyn stinh ta la tb lb)
      = ReductionStateLabelBox tz syn inh stsyn stinh ta la tb lb

    treeLabel (ReductionStateBox x) = ReductionStateLabelBox $ treeLabel' x
      where
        treeLabel'
          :: ReductionState tag tz syn inh stsyn stinh ta la tb lb
          -> ReductionStateLabel tag tz syn inh stsyn stinh ta la tb lb
        treeLabel' (AttrState z as)      = AttrStateLabel z as
        treeLabel' (RankedTreeState l _) = RankedTreeStateLabel l
        treeLabel' (StackHeadState _)    = StackHeadStateLabel
        treeLabel' (StackConsState _ _)  = StackConsStateLabel
        treeLabel' (StackTailState _)    = StackTailStateLabel
        treeLabel' StackEmptyState       = StackEmptyStateLabel

    treeChilds (ReductionStateBox x) = treeChilds' x
      where
        treeChilds'
          :: ReductionState tag tz syn inh stsyn stinh ta la tb lb
          -> (NodeVec :$ ReductionStateBox tz syn inh stsyn stinh ta la tb lb)
        treeChilds' (AttrState _ _)        = []
        treeChilds' (RankedTreeState _ ts) = ReductionStateBox <$> ts
        treeChilds' (StackHeadState t)     = [ReductionStateBox t]
        treeChilds' (StackConsState h t)   = [ReductionStateBox h, ReductionStateBox t]
        treeChilds' (StackTailState t)     = [ReductionStateBox t]
        treeChilds' StackEmptyState        = []

    treeLabelRank _ (ReductionStateLabelBox l) = treeLabelRank' l
      where
        treeLabelRank'
          :: ReductionStateLabel tag tz syn inh stsyn stinh ta la tb lb -> RankNumber
        treeLabelRank' (AttrStateLabel _ _)      = 0
        treeLabelRank' (RankedTreeStateLabel lb) = treeLabelRank (treeTag @tb) lb
        treeLabelRank' StackHeadStateLabel       = 1
        treeLabelRank' StackConsStateLabel       = 2
        treeLabelRank' StackTailStateLabel       = 1
        treeLabelRank' StackEmptyStateLabel      = 0

    mkTreeUnchecked (ReductionStateLabelBox l) = ReductionStateBox . mkTreeUnchecked' l
      where
        outReductionStateBoxUnsafe = taggedEither id
          (const $ error "not permitted operation") . reductionStateBox

        stkReductionStateBoxUnsafe = taggedEither
          (const $ error "not permitted operation") id . reductionStateBox

        mkTreeUnchecked'
          :: ReductionStateLabel tag tz syn inh stsyn stinh ta la tb lb
          -> (NodeVec :$ ReductionStateBox tz syn inh stsyn stinh ta la tb lb)
          -> ReductionState tag tz syn inh stsyn stinh ta la tb lb
        mkTreeUnchecked' (AttrStateLabel z s)      _  = AttrState z s
        mkTreeUnchecked' (RankedTreeStateLabel lb) ts = RankedTreeState lb
          $ outReductionStateBoxUnsafe <$> ts
        mkTreeUnchecked' StackHeadStateLabel       ts = StackHeadState
          (stkReductionStateBoxUnsafe $ ts ! 0)
        mkTreeUnchecked' StackConsStateLabel       ts = StackConsState
          (outReductionStateBoxUnsafe $ ts ! 0)
          (stkReductionStateBoxUnsafe $ ts ! 1)
        mkTreeUnchecked' StackTailStateLabel       ts = StackTailState
          (stkReductionStateBoxUnsafe $ ts ! 0)
        mkTreeUnchecked' StackEmptyStateLabel      _  = StackEmptyState


applyRHSToState :: forall tag tz syn inh stsyn stinh ta tb.
  (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => TreeRightHandSide tag syn inh stsyn stinh tb
  -> InputRankedTreeZipper tz ta -> [RankNumber]
  -> TreeReductionState tag tz syn inh stsyn stinh ta tb
applyRHSToState rhs z p = go rhs where
  go :: TreeRightHandSide tg syn inh stsyn stinh tb -> TreeReductionState tg tz syn inh stsyn stinh ta tb
  go (AttrSide abox)           = go' $ toReductionAttrState abox p
  go (LabelSide l cs)          = RankedTreeState l $ go <$> cs
  go (StackHeadSide srhs)      = StackHeadState $ go srhs
  go (StackConsSide orhs srhs) = StackConsState (go orhs) (go srhs)
  go (StackTailSide srhs)      = StackTailState $ go srhs
  go StackEmptySide            = StackEmptyState

  go' :: ReductionAttrState tg syn inh stsyn stinh -> TreeReductionState tg tz syn inh stsyn stinh ta tb
  go' state = AttrState (fromMaybe z $ nextTz state z) state

  nextTz :: ReductionAttrState tg syn inh stsyn stinh -> InputRankedTreeZipper tz ta -> Maybe (InputRankedTreeZipper tz ta)
  nextTz (ReductionOutAttrState abox p') = nextTz' abox p'
  nextTz (ReductionStkAttrState abox p') = nextTz' abox p'
  nextTz _                               = unreachable

  nextTz' :: AttAttrEitherBox sa ia -> [RankNumber] -> InputRankedTreeZipper tz ta -> Maybe (InputRankedTreeZipper tz ta)
  nextTz' (TaggedSynBox _) []    = zoomInRtZipper
  nextTz' (TaggedSynBox _) (n:_) = zoomInIdxRtZipper n
  nextTz' (TaggedInhBox _) _     = zoomOutRtZipper
  nextTz' _                _     = unreachable

type TreeReductionStateZipper tz syn inh stsyn stinh ta tb
  = tz (TreeReductionStateBox tz syn inh stsyn stinh ta tb) (TreeReductionStateLabelBox tz syn inh stsyn stinh ta tb)


-- reduction systems

buildSattReduction :: forall b tz syn inh stsyn stinh ta tb.
  (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => (b -> TreeReductionStateZipper tz syn inh stsyn stinh ta tb -> b)
  -> b
  -> ReductionOutAttrState syn inh stsyn stinh
  -> StackAttrTreeTrans syn inh stsyn stinh ta tb
  -> InputRankedTree ta -> b
buildSattReduction f s is StackAttrTreeTrans{..} t = goTop s where
  applyAttrToState
    :: InputRankedTreeZipper tz ta
    -> ReductionAttrState tag syn inh stsyn stinh
    -> TreeReductionState tag tz syn inh stsyn stinh ta tb
  applyAttrToState tz attrState =
    let l = treeLabel $ toTree tz
        (rhs, p) = applyAttrToRule l attrState
    in applyRHSToState rhs tz p

  applyAttrToRule
    :: InputLabelType ta
    -> ReductionAttrState tag syn inh stsyn stinh
    -> (TreeRightHandSide tag syn inh stsyn stinh tb, [RankNumber])
  applyAttrToRule l (ReductionAttrState abox p) =
    first (\a -> reductionRule a l) $ toInputAttr abox p

  goTop state =
    let taZ      = toZipper t
        stateZ   = toZipper . ReductionStateBox $ AttrState taZ is
    in case is of
      ReductionOutAttrState (TaggedInhBox _) [] -> f state stateZ
      _                                         -> go' state stateZ

  go !state stateZ = case nextStateZ stateZ of
    Nothing      -> f state stateZ
    Just nstateZ -> go' state nstateZ

  go' state stateZ =
    let nstate   = f state stateZ
        stateZ' = reductState stateZ $ toTree stateZ
    in go nstate stateZ'

  reductState stZ (ReductionStateBox x) = case x of
    AttrState taZ attrState -> setTreeZipper (ReductionStateBox $ applyAttrToState taZ attrState) stZ
    StackConsState hd tl    -> deconstractStack hd tl stZ
    _                       -> error "not permitted operation"

  deconstractStack
    :: TreeReductionOutState tz syn inh stsyn stinh ta tb
    -> TreeReductionStkState tz syn inh stsyn stinh ta tb
    -> TreeReductionStateZipper tz syn inh stsyn stinh ta tb
    -> TreeReductionStateZipper tz syn inh stsyn stinh ta tb
  deconstractStack hd tl stateZ = case zoomOutRtZipper stateZ of
    Nothing      -> error "not permitted operation"
    Just nstateZ -> case toTree nstateZ of
      ReductionStateBox x -> case x of
        StackHeadState _ -> setTreeZipper (ReductionStateBox hd) nstateZ
        StackTailState _ -> setTreeZipper (ReductionStateBox tl) nstateZ
        _                -> error "not permitted operation"

  nextStateZ = runKleisli nextStateZ'

  nextStateZ'
    =   Kleisli filterStateZipper
    <+> (Kleisli zoomInRtZipper >>> nextStateZ')
    <+> nextStateZ''

  filterStateZipper stateZ = case toTree stateZ of
    ReductionStateBox x -> filterStateZipper' stateZ x

  filterStateZipper' :: a -> TreeReductionState tag tz syn inh stsyn stinh ta tb -> Maybe a
  filterStateZipper' _   (RankedTreeState _ _) = empty
  filterStateZipper' _   (StackHeadState _)    = empty
  filterStateZipper' _   (StackTailState _)    = empty
  filterStateZipper' _   StackEmptyState       = empty
  filterStateZipper' _   (AttrState _ (ReductionOutAttrState (TaggedInhBox _) [])) = empty
  filterStateZipper' _   (AttrState _ (ReductionStkAttrState (TaggedInhBox _) [])) = empty
  filterStateZipper' stZ _ = pure stZ

  nextStateZ''
    =   (Kleisli zoomRightRtZipper >>> nextStateZ')
    <+> (Kleisli zoomOutRtZipper   >>> nextStateZ'')

runSattReduction :: forall tz syn inh stsyn stinh ta tb.
  (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => ReductionOutAttrState syn inh stsyn stinh -> StackAttrTreeTrans syn inh stsyn stinh ta tb
  -> InputRankedTree ta -> TreeReductionStateBox tz syn inh stsyn stinh ta tb
runSattReduction is trans t = toTopTree $ builder t where
  initialStateZ = toZipper . ReductionStateBox $ AttrState (toZipper t) is

  builder = buildSattReduction (const id) initialStateZ is trans


type InputAttrBox syn inh stsyn stinh
  = SattAttrEitherBox (ATT.InputAttr syn inh) (ATT.InputAttr stsyn stinh)

inputAttrBox :: InputAttr tag syn inh stsyn stinh -> InputAttrBox syn inh stsyn stinh
inputAttrBox = TaggedEitherBox

data ReductionStep syn inh stsyn stinh t l
  = AttrReductionStep (InputAttrBox syn inh stsyn stinh) l [RankNumber]
  | StackHeadConsDeconstract
  | StackTailConsDeconstract
  deriving (Eq, Ord)

instance (Show syn, Show inh, Show stsyn, Show stinh, Show l)
  => Show (ReductionStep syn inh stsyn stinh t l) where
    show StackHeadConsDeconstract  = "HC"
    show StackTailConsDeconstract  = "TC"
    show (AttrReductionStep a l p) = showAttrStep a
      where
        showAttrStep (TaggedOutBox a') = showAttr a'
          <> " ={" <> show l <> "," <> show (reverse p) <> "}=> "
        showAttrStep (TaggedStkBox a') = showAttr a'
          <> " ={" <> show l <> "," <> show (reverse p) <> "}=> "
        showAttrStep _                 = unreachable

        showAttr (TaggedSynBox a') = show a'
        showAttr (TaggedInhBox a') = show a'
        showAttr _                 = unreachable


type TreeReductionStep syn inh stsyn stinh t = RtApply (ReductionStep syn inh stsyn stinh) t

data ReductionStateStep tz syn inh stsyn stinh ta la tb lb = ReductionStateStep
  { reductionStepState :: ReductionStateBox tz syn inh stsyn stinh ta la tb lb
  , reductionStateStep :: ReductionStep syn inh stsyn stinh
    (RankedTreeWithInitial ta la) (RankedTreeLabelWithInitial ta la)
  }

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show stsyn, Show stinh, Show la, Show lb)
  => Show (ReductionStateStep tz syn inh stsyn stinh ta la tb lb) where
    show (ReductionStateStep state step) = show state <> " =" <> showStep step <> "=> "
      where
        showStep (AttrReductionStep _ l p) = showStep' l p
        showStep StackHeadConsDeconstract  = "HC"
        showStep StackTailConsDeconstract  = "TC"

        showStep' l p = "{" <> show l <> "," <> show (reverse p) <> "}"

data ReductionSteps tz syn inh stsyn stinh ta la tb lb = ReductionSteps
  { reductionSteps  :: [ReductionStateStep tz syn inh stsyn stinh ta la tb lb]
  , reductionResult :: ReductionStateBox tz syn inh stsyn stinh ta la tb lb
  }

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show stsyn, Show stinh, Show la, Show lb)
  => Show (ReductionSteps tz syn inh stsyn stinh ta la tb lb) where
    show (ReductionSteps steps res) = intercalate "" (show <$> steps) <> show res

type TreeReductionSteps tz syn inh stsyn stinh ta tb = RtApply (RtApply (ReductionSteps tz syn inh stsyn stinh) ta) tb

buildStepFromAttrState :: forall tag syn inh stsyn stinh t.
  (RankedTree t)
  => LabelType t -> ReductionAttrState tag syn inh stsyn stinh -> TreeReductionStep syn inh stsyn stinh t
buildStepFromAttrState l (ReductionAttrState abox p) =
    let (a, p') = toInputAttr abox p
    in AttrReductionStep (inputAttrBox a) l p'

buildSattReductionSteps :: forall tz syn inh stsyn stinh ta tb.
  (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => ReductionOutAttrState syn inh stsyn stinh
  -> StackAttrTreeTrans syn inh stsyn stinh ta tb
  -> InputRankedTree ta -> TreeReductionSteps tz syn inh stsyn stinh ta tb
buildSattReductionSteps is trans = buildSteps
    . buildSattReduction builder ([], Nothing) is trans
  where
    buildSteps = uncurry ReductionSteps <<< reverse *** (toTopTree . fromMaybe (error "unexpected operation"))

    builder (steps, Just sz) stateZ = (buildStepFromStateZ sz : steps, Just stateZ)
    builder (steps, Nothing) stateZ = (steps, Just stateZ)

    buildStepFromStateZ stateZ =
      let stateStep = case toTree stateZ of
            ReductionStateBox x -> case x of
              AttrState taZ attrState -> buildStepFromAttrState (getTreeLabel taZ) attrState
              StackConsState _ _      -> case toTree <$> zoomOutRtZipper stateZ of
                Just (ReductionStateBox (StackHeadState _)) -> StackHeadConsDeconstract
                Just (ReductionStateBox (StackTailState _)) -> StackTailConsDeconstract
                _ -> error "unexpected operation"
              _ -> error "unexpected operation"
      in ReductionStateStep (toTopTree stateZ) stateStep

buildSattReductionSteps' :: forall tz syn inh stsyn stinh ta tb.
  (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => (StackAttrTreeTrans syn inh stsyn stinh ta tb -> ReductionOutAttrState syn inh stsyn stinh)
  -> StackAttrTreeTrans syn inh stsyn stinh ta tb
  -> InputRankedTree ta -> TreeReductionSteps tz syn inh stsyn stinh ta tb
buildSattReductionSteps' f trans = buildSattReductionSteps (f trans) trans

-- tree transducer

instance TreeTransducer (StackAttrTreeTrans syn inh stsyn stinh) where
  treeTrans trans = render
      . runSattReduction @RTZipper (initialSattReductionState trans) trans
      . toRankedTreeWithInitial
    where
      render = fromMaybe (error "The input tree transducer is illegal.")
        . fromTreeReductionStateBox

      fromTreeReductionStateBox :: RankedTree tb => TreeReductionStateBox tz syn inh stsyn stinh ta tb -> Maybe tb
      fromTreeReductionStateBox (ReductionStateBox x) = fromTreeReductionState x

-- bottom label

bottomLabelSide :: RankedTree t => TreeOutRightHandSide syn inh stsyn stinh t
bottomLabelSide = LabelSide bottomLabel empty
