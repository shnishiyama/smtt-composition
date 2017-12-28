{-# LANGUAGE NoStrict        #-}
{-# LANGUAGE NoStrictData    #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.MAC where

import           SattPrelude

import           Data.Functor.Foldable
import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.Class


data RightHandSideF s l t c rhs
  = MttContext !c
  | MttState !s !t !(NodeVec rhs)
  | MttLabelSide l !(NodeVec rhs)
  deriving (Eq, Ord, Show, Generic, Generic1)

deriveEq1 ''RightHandSideF
deriveEq2 ''RightHandSideF
deriveOrd1 ''RightHandSideF
deriveOrd2 ''RightHandSideF
deriveShow1 ''RightHandSideF
deriveShow2 ''RightHandSideF


type RightHandSide s l = Fix (RightHandSideF s l RankNumber RankNumber)

bottomLabelSide :: RightHandSide s l
bottomLabelSide = Fix $ MttLabelSide bottomLabel []

data MacroTreeTransducer s ta la tb lb = MacroTreeTransducer
  { mttStates      :: HashSet s
  , mttInitialExpr :: RightHandSide s lb
  , mttTransRules  :: HashMap (s, la) (RightHandSide s lb)
  } deriving (Eq, Show, Generic)

buildMtt
  :: HashSet s -> RightHandSide s lb -> HashMap (s, la) (RightHandSide s lb)
  -> MacroTreeTransducer s ta la tb lb
buildMtt = MacroTreeTransducer

type MttConstraint s ta la tb lb =
  ( RtConstraint ta la
  , RtConstraint tb lb
  , Eq s, Hashable s, RankedLabel s
  , Eq la, Hashable la
  )

mttTranslateRule :: MttConstraint s ta la tb lb
  => MacroTreeTransducer s ta la tb lb -> (s, la) -> RightHandSide s lb
mttTranslateRule trans p = fromMaybe bottomLabelSide . lookup p $ mttTransRules trans


-- reduction system

newtype ReductionStateF s ta la tb lb state = ReductionStateF
  { unwrapReductionStateF :: RightHandSideF s lb ta state state
  } deriving (Eq, Ord, Show, Generic)

instance (Eq s, Eq lb, Eq ta) => Eq1 (ReductionStateF s ta la tb lb) where
  liftEq f (ReductionStateF x1) (ReductionStateF x2) = liftEq2 f f x1 x2

instance (Ord s, Ord lb, Ord ta) => Ord1 (ReductionStateF s ta la tb lb) where
  liftCompare f (ReductionStateF x1) (ReductionStateF x2) = liftCompare2 f f x1 x2

instance (Show s, Show lb, Show ta) => Show1 (ReductionStateF s ta la tb lb) where
  liftShowsPrec sPrec sList i (ReductionStateF x) = liftShowsPrec2 sPrec sList sPrec sList i x

type ReductionState s ta la tb lb = Fix (ReductionStateF s ta la tb lb)

pattern RedFix
  :: RightHandSideF s lb ta (ReductionState s ta la tb lb) (ReductionState s ta la tb lb)
  -> ReductionState s ta la tb lb
pattern RedFix s = Fix (ReductionStateF s)
{-# COMPLETE RedFix #-}

buildMttReduction :: a
buildMttReduction = undefined

runMttReduction :: MttConstraint s ta la tb lb
  => MacroTreeTransducer s ta la tb lb -> ReductionState s ta la tb lb -> ReductionState s ta la tb lb
runMttReduction = undefined


-- The instance for mtt
instance MttConstraint s ta la tb lb => TreeTransducer (MacroTreeTransducer s ta la tb lb) ta tb where
  treeTrans trans = fromReductionState . runMttReduction trans . toReductionState (mttInitialExpr trans)
    where
      toReductionState (Fix ie) t = case ie of
        MttLabelSide l cs -> RedFix $ MttLabelSide l $ flip toReductionState t <$> cs
        MttState f _ cs   -> RedFix $ MttState f t $ flip toReductionState t <$> cs
        MttContext{}      -> error "This tree transducer is illegal."

      fromReductionState (RedFix (MttLabelSide l cs)) = mkTreeUnchecked l $ fromReductionState <$> cs
      fromReductionState _ = error "This tree transducer is illegal."
