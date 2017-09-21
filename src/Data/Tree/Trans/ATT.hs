{-# LANGUAGE FlexibleInstances #-}

module Data.Tree.Trans.ATT
  (
    -- att attribute tags
    AttAttrTag
  , SynAttrTag
  , InhAttrTag
  , TaggedSyn
  , TaggedInh
  , AttAttrEither
  , taggedSyn
  , taggedInh
  , pattern TaggedSyn
  , pattern TaggedInh
  , AttAttrEitherBox
  , taggedSynBox
  , taggedInhBox
  , pattern TaggedSynBox
  , pattern TaggedInhBox

    -- common
  , InputLabelType
  , InputRankedTree
  , InputRankedTreeZipper
  , RightHandSide(..)
  , AttrSide
  , synAttrSide
  , inhAttrSide
  , TreeRightHandSide
  , InputAttr
  , pattern SynAttr
  , pattern InhAttr
  , toInputAttr
  , AttRuleType
  , AttrTreeTrans(..)
  , FinAttRuleType
  , AttRuleInputParams(..)
  , FiniteInputRankedTree
  , FiniteAttrTreeTrans(..)
  , FiniteAttrTreeTransReq
  , fromFunctionBase
  , FuncBasedAttrTreeTrans(..)
  , projAttrTreeTrans
  , WrappedAttrTreeTrans(..)

    -- reduction state
  , ReductionAttrState(..)
  , initialAttReductionState
  , ReductionState(..)
  , TreeReductionState
  , fromTreeReductionState
  , ReductionStateLabel(..)
  , TreeReductionStateLabel

    -- reduction system
  , buildAttReduction
  , runAttReduction
  , ReductionStep(..)
  , TreeReductionStep
  , ReductionStateStep(..)
  , ReductionSteps(..)
  , TreeReductionSteps
  , buildAttReductionSteps
  , buildAttReductionSteps'

    -- bottom label
  , bottomLabelSide
  ) where

import           ClassyPrelude

import           Control.Arrow               hiding (first, second)
import           Data.Profunctor.Unsafe
import           Data.Coerce
import           Data.TypeLevel.TaggedEither
import           Data.Universe.Class
import qualified Data.HashMap.Strict as HM

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Zipper
import           Data.Tree.Trans.Class

-- attibute kinds

type AttAttrTag = EitherTag

type SynAttrTag = 'LeftTag
type InhAttrTag = 'RightTag

type TaggedSyn = AttAttrEither SynAttrTag
type TaggedInh = AttAttrEither InhAttrTag

type AttAttrEither = TaggedEither
type AttAttrEitherBox = TaggedEitherBox

taggedSyn :: syn -> TaggedSyn syn inh
taggedSyn = TaggedLeft

taggedInh :: inh -> TaggedInh syn inh
taggedInh = TaggedRight

taggedSynBox :: syn -> AttAttrEitherBox syn inh
taggedSynBox = taggedLeftBox

taggedInhBox :: inh -> AttAttrEitherBox syn inh
taggedInhBox = taggedRightBox

pattern TaggedSyn
  :: () => tag ~ SynAttrTag
  => syn -> AttAttrEither tag syn inh
pattern TaggedSyn x = TaggedLeft x

pattern TaggedInh
  :: () => tag ~ 'RightTag
  => inh -> AttAttrEither tag syn inh
pattern TaggedInh x = TaggedRight x

{-# COMPLETE TaggedSyn, TaggedInh #-}

pattern TaggedSynBox :: syn -> AttAttrEitherBox syn inh
pattern TaggedSynBox x = TaggedLeftBox x

pattern TaggedInhBox :: inh -> AttAttrEitherBox syn inh
pattern TaggedInhBox x = TaggedRightBox x

{-# COMPLETE TaggedSynBox, TaggedInhBox #-}

-- common

type RTZipperWithInitial tz t l = tz (RankedTreeWithInitial t l) (RankedTreeLabelWithInitial t l)

type InputLabelType t = RtApply RankedTreeLabelWithInitial t
type InputRankedTree t = RtApply RankedTreeWithInitial t
type InputRankedTreeZipper tz t = RTZipperWithInitial tz t (LabelType t)

type AttrSide syn inh = AttAttrEitherBox (syn, RankNumber) inh

data RightHandSide syn inh t l
  = AttrSide (AttrSide syn inh)
  | LabelSide l (NodeVec :$ RightHandSide syn inh t l)
  deriving (Show, Eq, Ord, Generic)

synAttrSide :: syn -> RankNumber -> RightHandSide syn inh t l
synAttrSide a i = AttrSide $ taggedSynBox (a, i)

inhAttrSide :: inh -> RightHandSide syn inh t l
inhAttrSide a = AttrSide $ taggedInhBox a

type TreeRightHandSide syn inh t = RtApply (RightHandSide syn inh) t

type InputAttr syn inh = AttAttrEitherBox syn (inh, RankNumber)

pattern SynAttr :: syn -> InputAttr syn inh
pattern SynAttr a = TaggedSynBox a

pattern InhAttr :: inh -> RankNumber -> InputAttr syn inh
pattern InhAttr b i = TaggedInhBox (b, i)

{-# COMPLETE SynAttr, InhAttr #-}

toInputAttr :: AttAttrEitherBox syn inh -> [RankNumber] -> (InputAttr syn inh, [RankNumber])
toInputAttr (TaggedSynBox a) p      = (taggedSynBox a, p)
toInputAttr (TaggedInhBox a) (x:xs) = (taggedInhBox (a, x), xs)
toInputAttr _                _      = error "an inherited attribute has empty path"

type AttRuleType syn inh ta tb
  = InputAttr syn inh -> InputLabelType ta -> TreeRightHandSide syn inh tb

-- | The class of attributed tree transducer
class (RankedTree ta, RankedTree tb, TreeTransducer t ta tb) => AttrTreeTrans t ta tb | t -> ta, t -> tb where
  type SynthesAttr t :: *
  type InheritAttr t :: *

  initialAttr :: t -> SynthesAttr t
  reductionRule :: t -> AttRuleType (SynthesAttr t) (InheritAttr t) ta tb

-- | A finite attributed tree transducer by hashmap based
type FinAttRuleType syn inh ta tb = HashMap (InputAttr syn inh, InputLabelType ta) (TreeRightHandSide syn inh tb)

data FiniteAttrTreeTrans syn inh ta tb = FinAttrTreeTrans
  { finInitialAttr :: syn
  , finReductionRule :: FinAttRuleType syn inh ta tb
  }

deriving instance (Eq syn, Eq inh, Eq (LabelType ta), Eq (LabelType tb))
  => Eq (FiniteAttrTreeTrans syn inh ta tb)
deriving instance (Show syn, Show inh, Show (LabelType ta), Show (LabelType tb))
  => Show (FiniteAttrTreeTrans syn inh ta tb)

type FinInputRankedTree t l = (Eq l, Hashable l, FinRankedTree t l)
type FiniteInputRankedTree t = FinInputRankedTree t (LabelType t)

type FiniteAttrTreeTransReq syn inh ta tb =
  ( Eq syn, Eq inh, Hashable syn, Hashable inh
  , Finite syn, Finite inh
  , FiniteInputRankedTree ta, RankedTree tb
  )

instance FiniteAttrTreeTransReq syn inh ta tb
    => AttrTreeTrans (FiniteAttrTreeTrans syn inh ta tb) ta tb where

  type SynthesAttr (FiniteAttrTreeTrans syn inh ta tb) = syn
  type InheritAttr (FiniteAttrTreeTrans syn inh ta tb) = inh

  initialAttr = finInitialAttr
  reductionRule t = let !r = finReductionRule t in \a i -> r ! (a, i)

instance FiniteAttrTreeTransReq syn inh ta tb
    => TreeTransducer (FiniteAttrTreeTrans syn inh ta tb) ta tb where

  treeTrans = treeTrans .# wrapAttrTreeTrans

newtype AttRuleInputParams syn inh ta tb = AttRuleInputParams
  (InputAttr syn inh, InputLabelType ta)
  deriving (Generic)

deriving instance (Eq syn, Eq inh, Eq (LabelType ta)) => Eq (AttRuleInputParams syn inh ta tb)
deriving instance (Ord syn, Ord inh, Ord (LabelType ta)) => Ord (AttRuleInputParams syn inh ta tb)
deriving instance (Show syn, Show inh, Show (LabelType ta)) => Show (AttRuleInputParams syn inh ta tb)

instance (Universe syn, Universe inh, RankedTree ta, Universe (LabelType ta))
    => Universe (AttRuleInputParams syn inh ta tb) where

  universe = do
    l <- universe
    let r = treeLabelRank (treeTag @(RankedTreeWithInitial ta (LabelType ta))) l
    a <- [taggedSynBox a | a <- universe] <> [taggedInhBox (a, i) | a <- universe, i <- [0..(r - 1)]]
    return $ AttRuleInputParams (a, l)

instance (Finite syn, Finite inh, RankedTree ta, Finite (LabelType ta))
    => Finite (AttRuleInputParams syn inh ta tb)

fromFunctionBase :: FiniteAttrTreeTransReq syn inh ta tb
  => AttRuleType syn inh ta tb -> FinAttRuleType syn inh ta tb
fromFunctionBase f = HM.fromList [(x, f a l) | AttRuleInputParams x@(a, l) <- universeF]

-- | An attributed tree transducer by function based (old and runtime representation)
data FuncBasedAttrTreeTrans syn inh ta tb = FBAttrTreeTrans
  { fbInitialAttr   :: syn
  , fbReductionRule :: AttRuleType syn inh ta tb
  }

projAttrTreeTrans :: AttrTreeTrans t ta tb => t -> FuncBasedAttrTreeTrans (SynthesAttr t) (InheritAttr t) ta tb
projAttrTreeTrans t = FBAttrTreeTrans (initialAttr t) (reductionRule t)

instance (RankedTree ta, RankedTree tb) => AttrTreeTrans (FuncBasedAttrTreeTrans syn inh ta tb) ta tb where
  type SynthesAttr (FuncBasedAttrTreeTrans syn inh ta tb) = syn
  type InheritAttr (FuncBasedAttrTreeTrans syn inh ta tb) = inh

  initialAttr = fbInitialAttr
  reductionRule = fbReductionRule

instance (RankedTree ta, RankedTree tb) => TreeTransducer (FuncBasedAttrTreeTrans syn inh ta tb) ta tb where
  treeTrans = treeTrans .# wrapAttrTreeTrans

-- reduction states

data ReductionAttrState syn inh = ReductionAttrState
  { reductionAttrState :: AttAttrEitherBox syn inh
  , reductionPathState :: [RankNumber]
  } deriving (Eq, Ord)

instance (Show syn, Show inh) => Show (ReductionAttrState syn inh) where
  show (ReductionAttrState abox p) = case abox of
      TaggedSynBox a -> showAttrState a
      TaggedInhBox a -> showAttrState a
    where
      showAttrState :: Show a => a -> String
      showAttrState x = show x <> show (reverse p)

data ReductionState tz syn inh ta la tb lb
  = AttrState (RTZipperWithInitial tz ta la) (ReductionAttrState syn inh)
  | RankedTreeState lb (NodeVec :$ ReductionState tz syn inh ta la tb lb)

instance (Eq syn, Eq inh, Eq lb, RtConstraint tb lb)
  => Eq (ReductionState tz syn inh ta la tb lb) where
    t1 == t2 = wrapRankedTree t1 == wrapRankedTree t2

instance (Ord syn, Ord inh, Ord lb, RtConstraint tb lb)
  => Ord (ReductionState tz syn inh ta la tb lb) where
    t1 `compare` t2 = wrapRankedTree t1 `compare` wrapRankedTree t2

instance (Show syn, Show inh, Show lb, RtConstraint tb lb)
  => Show (ReductionState tz syn inh ta la tb lb) where
    show = show .# wrapRankedTree

type TreeReductionState tz syn inh ta tb = RtApply (RtApply (ReductionState tz syn inh) ta) tb

fromTreeReductionState :: RankedTree tb => TreeReductionState tz syn inh ta tb -> Maybe tb
fromTreeReductionState (RankedTreeState l ss) = pure (mkTree l) <*> traverse fromTreeReductionState ss
fromTreeReductionState _                      = empty

initialAttReductionState :: FuncBasedAttrTreeTrans syn inh ta tb -> ReductionAttrState syn inh
initialAttReductionState t = ReductionAttrState (taggedSynBox $ fbInitialAttr t) []

toReductionAttrState :: AttrSide syn inh -> [RankNumber] -> ReductionAttrState syn inh
toReductionAttrState (TaggedSynBox (a, i)) p = ReductionAttrState (taggedSynBox a) (i:p)
toReductionAttrState (TaggedInhBox a)     p = ReductionAttrState (taggedInhBox a) p


data ReductionStateLabel tz syn inh ta la tb lb
  = AttrStateLabel (RTZipperWithInitial tz ta la) (ReductionAttrState syn inh)
  | RankedTreeStateLabel lb

instance (Eq syn, Eq inh, Eq lb) => Eq (ReductionStateLabel tz syn inh ta la tb lb) where
  AttrStateLabel _ as1    == AttrStateLabel _ as2    = as1 == as2
  RankedTreeStateLabel l1 == RankedTreeStateLabel l2 = l1 == l2
  _ == _ = False

instance (Ord syn, Ord inh, Ord lb) => Ord (ReductionStateLabel tz syn inh ta la tb lb) where
  AttrStateLabel _ as1    `compare` AttrStateLabel _ as2    = as1 `compare` as2
  RankedTreeStateLabel l1 `compare` RankedTreeStateLabel l2 = l1 `compare` l2
  AttrStateLabel _ _ `compare` _ = LT
  _                  `compare` _ = GT

instance (Show syn, Show inh, Show lb) => Show (ReductionStateLabel tz syn inh ta la tb lb) where
  show (AttrStateLabel _ a)     = show a
  show (RankedTreeStateLabel l) = show l

type TreeReductionStateLabel tz syn inh ta tb
  = RtApply (RtApply (ReductionStateLabel tz syn inh) ta) tb


instance (RtConstraint tb lb)
  => RankedTree (ReductionState tz syn inh ta la tb lb) where

    type LabelType (ReductionState tz syn inh ta la tb lb)
      = ReductionStateLabel tz syn inh ta la tb lb

    treeLabel (AttrState z s)       = AttrStateLabel z s
    treeLabel (RankedTreeState l _) = RankedTreeStateLabel l

    treeChilds (AttrState _ _)        = empty
    treeChilds (RankedTreeState _ ts) = ts

    treeLabelRank _ (AttrStateLabel _ _)     = 0
    treeLabelRank _ (RankedTreeStateLabel l) = treeLabelRank (treeTag @tb) l

    mkTreeUnchecked (AttrStateLabel z s)     _  = AttrState z s
    mkTreeUnchecked (RankedTreeStateLabel l) ts = RankedTreeState l ts


applyRHSToState :: (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => TreeRightHandSide syn inh tb
  -> InputRankedTreeZipper tz ta -> [RankNumber]
  -> TreeReductionState tz syn inh ta tb
applyRHSToState rhs z p = go rhs where
  go (AttrSide abox)  = go' $ toReductionAttrState abox p
  go (LabelSide l cs) = RankedTreeState l $ go <$> cs

  go' state = AttrState (fromMaybe z $ nextTz state z) state

  nextTz (ReductionAttrState (TaggedInhBox _) _)     = zoomOutRtZipper
  nextTz (ReductionAttrState (TaggedSynBox _) [])    = zoomInRtZipper
  nextTz (ReductionAttrState (TaggedSynBox _) (n:_)) = zoomInIdxRtZipper n

type TreeReductionStateZipper tz syn inh ta tb
  = tz (TreeReductionState tz syn inh ta tb) (TreeReductionStateLabel tz syn inh ta tb)


-- reduction systems

buildAttReduction :: forall b tz syn inh ta tb.
  (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => (b -> TreeReductionStateZipper tz syn inh ta tb -> b)
  -> b
  -> ReductionAttrState syn inh
  -> FuncBasedAttrTreeTrans syn inh ta tb
  -> InputRankedTree ta -> b
buildAttReduction f s is FBAttrTreeTrans{..} t = goTop s
  where
    applyAttrToState tz attrState =
      let l        = treeLabel $ toTree tz
          (rhs, p) = applyAttrToRule l attrState
      in applyRHSToState rhs tz p

    applyAttrToRule l (ReductionAttrState abox p) =
      first (\a -> fbReductionRule a l) $ toInputAttr abox p

    goTop state =
      let taZ      = toZipper t
          stateZ   = toZipper $ AttrState taZ is
      in case is of
        ReductionAttrState (TaggedInhBox _) [] -> f state stateZ
        _                                      -> go' state stateZ

    go !state stateZ = case nextStateZ stateZ of
        Nothing      -> f state stateZ
        Just nstateZ -> go' state nstateZ

    go' state stateZ =
      let nstate  = f state stateZ
          stateZ' = reductState stateZ $ toTree stateZ
      in go nstate stateZ'

    reductState stZ (AttrState taZ attrState) = setTreeZipper (applyAttrToState taZ attrState) stZ
    reductState _   _                         = error "not permitted operation"

    nextStateZ = runKleisli nextStateZ'

    nextStateZ'
      =   Kleisli filterStateZipper
      <+> (Kleisli zoomInRtZipper >>> nextStateZ')
      <+> nextStateZ''

    filterStateZipper stateZ = case toTree stateZ of
      RankedTreeState{}                                    -> empty
      AttrState _ (ReductionAttrState (TaggedInhBox _) []) -> empty
      _                                                    -> pure stateZ

    nextStateZ''
      =   (Kleisli zoomRightRtZipper >>> nextStateZ')
      <+> (Kleisli zoomOutRtZipper   >>> nextStateZ'')

runAttReduction :: forall tz syn inh ta tb.
  (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => ReductionAttrState syn inh
  -> FuncBasedAttrTreeTrans syn inh ta tb
  -> InputRankedTree ta
  -> TreeReductionState tz syn inh ta tb
runAttReduction is trans t = toTopTree $ builder t where
  initialStateZ = toZipper $ AttrState (toZipper t) is

  builder = buildAttReduction (const id) initialStateZ is trans


data ReductionStep syn inh t l = ReductionStep
  { reductionStepInputAttr :: InputAttr syn inh
  , reductionStepLabel     :: l
  , reductionStepPath      :: [RankNumber]
  } deriving (Show, Eq, Ord)

type TreeReductionStep syn inh t = RtApply (ReductionStep syn inh) t

data ReductionStateStep tz syn inh ta la tb lb = ReductionStateStep
  { reductionStepState :: ReductionState tz syn inh ta la tb lb
  , reductionStateStep :: ReductionStep syn inh (RankedTreeWithInitial ta la) (RankedTreeLabelWithInitial ta la)
  }

deriving instance (Eq syn, Eq inh, Eq la, Eq lb, RtConstraint tb lb)
  => Eq (ReductionStateStep tz syn inh ta la tb lb)
deriving instance (Ord syn, Ord inh, Ord la, Ord lb, RtConstraint tb lb)
  => Ord (ReductionStateStep tz syn inh ta la tb lb)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show la, Show lb)
  => Show (ReductionStateStep tz syn inh ta la tb lb) where
    show (ReductionStateStep state step) = show state <> " =" <> showStep step <> "=> "
      where
        showStep (ReductionStep _ l p)   = showStep' l p

        showStep' l p = "{" <> show l <> "," <> show (reverse p) <> "}"

data ReductionSteps tz syn inh ta la tb lb = ReductionSteps
  { reductionSteps  :: [ReductionStateStep tz syn inh ta la tb lb]
  , reductionResult :: ReductionState tz syn inh ta la tb lb
  }

deriving instance (Eq syn, Eq inh, Eq la, Eq lb, RtConstraint tb lb)
  => Eq (ReductionSteps tz syn inh ta la tb lb)
deriving instance (Ord syn, Ord inh, Ord la, Ord lb, RtConstraint tb lb)
  => Ord (ReductionSteps tz syn inh ta la tb lb)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show la, Show lb, Show tb)
  => Show (ReductionSteps tz syn inh ta la tb lb) where
    show (ReductionSteps steps res) = intercalate "" (show <$> steps) <> show res

type TreeReductionSteps tz syn inh ta tb = RtApply (RtApply (ReductionSteps tz syn inh) ta) tb

buildStepFromAttrState :: RankedTree t
  => LabelType t -> ReductionAttrState syn inh -> TreeReductionStep syn inh t
buildStepFromAttrState l (ReductionAttrState abox p) =
  let (a, p') = toInputAttr abox p in ReductionStep a l p'

buildAttReductionSteps :: forall tz syn inh ta tb.
  (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => ReductionAttrState syn inh
  -> FuncBasedAttrTreeTrans syn inh ta tb
  -> InputRankedTree ta -> TreeReductionSteps tz syn inh ta tb
buildAttReductionSteps is trans = buildSteps
    . buildAttReduction builder ([], Nothing) is trans
  where
    buildSteps = uncurry ReductionSteps <<< reverse *** (toTopTree . fromMaybe (error "unexpected operation"))

    builder (steps, Just sz) stateZ = (buildStepFromStateZ sz : steps, Just stateZ)
    builder (steps, Nothing) stateZ = (steps, Just stateZ)

    buildStepFromStateZ stateZ =
      let AttrState taZ attrState = toTree stateZ
      in ReductionStateStep (toTopTree stateZ) $ buildStepFromAttrState (getTreeLabel taZ) attrState

buildAttReductionSteps' :: forall tz syn inh ta tb.
  (RankedTree ta, RankedTree tb, RankedTreeZipper tz)
  => (FuncBasedAttrTreeTrans syn inh ta tb -> ReductionAttrState syn inh)
  -> FuncBasedAttrTreeTrans syn inh ta tb
  -> InputRankedTree ta
  -> TreeReductionSteps tz syn inh ta tb
buildAttReductionSteps' f trans = buildAttReductionSteps (f trans) trans

-- tree transducer

newtype WrappedAttrTreeTrans t ta tb = WrappedAttrTreeTrans
  { unwrapAttrTreeTrans :: t
  }

wrapAttrTreeTrans :: AttrTreeTrans t ta tb => t -> WrappedAttrTreeTrans t ta tb
wrapAttrTreeTrans = coerce

instance (RankedTree ta, RankedTree tb, AttrTreeTrans t ta tb)
    => TreeTransducer (WrappedAttrTreeTrans t ta tb) ta tb where

  treeTrans trans = render
      . runAttReduction @ RTZipper (initialAttReductionState fbTrans) fbTrans
      . toRankedTreeWithInitial
    where
      fbTrans = projAttrTreeTrans $ unwrapAttrTreeTrans trans

      render = fromMaybe (error "The input tree transducer is illegal.")
        . fromTreeReductionState

-- bottom label

bottomLabelSide :: RankedTree t => TreeRightHandSide syn inh t
bottomLabelSide = LabelSide bottomLabel empty
