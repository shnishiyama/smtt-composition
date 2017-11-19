module Data.Tree.Trans.TOP where

import           ClassyPrelude

import           Data.Coerce
import           Data.Profunctor.Unsafe
import           Data.Tree.RankedTree
import           Data.Tree.Trans.Class

data RightHandSide s t l
  = State s RankNumber
  | LabelSide l (NodeVec :$ RightHandSide s t l)
  deriving (Show, Eq, Ord, Generic)

type TreeRightHandSide s t = RtApply (RightHandSide s) t


type TopDownRuleTypeBase s ta tb
  = LabelType ta -> TreeRightHandSide s tb

type TopDownRuleType t ta tb
  = TopDownRuleTypeBase (TdttStateType t) ta tb


-- | The class of top-down tree transducers
--
-- * initialState := State s 0 | ...
-- * reductionRule t := State s n | ... (0 <= n < treeRank t)
class (RankedTree ta, RankedTree tb, TreeTransducer t ta tb) => TopDownTreeTrans t ta tb | t -> ta, t -> tb where
  type TdttStateType t

  projTopDownTreeTrans :: t -> FuncBasedTopDownTreeTrans (TdttStateType t) ta tb

  initialState :: t -> TreeRightHandSide (TdttStateType t) tb
  reductionRule :: t -> TopDownRuleType t ta tb

type TdttConstraint t s ta tb =
  ( TopDownTreeTrans t ta tb
  , s ~ TdttStateType t
  )


data FuncBasedTopDownTreeTrans state ta tb = FbTopDownTreeTrans
  { fbInitialState  :: TreeRightHandSide state tb
  , fbReductionRule :: TopDownRuleTypeBase state ta tb
  }

instance (RankedTree ta, RankedTree tb) => TopDownTreeTrans (FuncBasedTopDownTreeTrans state ta tb) ta tb where
  type TdttStateType (FuncBasedTopDownTreeTrans state ta tb) = state

  projTopDownTreeTrans = id

  initialState = fbInitialState
  reductionRule = fbReductionRule

instance (RankedTree ta, RankedTree tb) => TreeTransducer (FuncBasedTopDownTreeTrans state ta tb) ta tb where
  treeTrans = treeTrans .# wrapTopDownTreeTrans

-- tree transducer

newtype WrappedTopDownTreeTrans t ta tb = WrappedTopDownTreeTrans
  { unwrapTopDownTreeTrans :: t
  } deriving (Eq, Ord, Show, Generic)

wrapTopDownTreeTrans :: TopDownTreeTrans t ta tb
  => t -> WrappedTopDownTreeTrans t ta tb
wrapTopDownTreeTrans = coerce
{-# INLINE wrapTopDownTreeTrans #-}

instance (RankedTree ta, RankedTree tb, TopDownTreeTrans t ta tb)
    => TopDownTreeTrans (WrappedTopDownTreeTrans t ta tb) ta tb where

  type TdttStateType (WrappedTopDownTreeTrans t ta tb) = TdttStateType t

  projTopDownTreeTrans (WrappedTopDownTreeTrans t) = projTopDownTreeTrans t

  initialState (WrappedTopDownTreeTrans t) = initialState t
  reductionRule (WrappedTopDownTreeTrans t) = reductionRule t

instance (RankedTree ta, RankedTree tb, TopDownTreeTrans t ta tb)
    => TreeTransducer (WrappedTopDownTreeTrans t ta tb) ta tb where

  treeTrans trans = undefined fbTrans
    where
      fbTrans = projTopDownTreeTrans $ unwrapTopDownTreeTrans trans
