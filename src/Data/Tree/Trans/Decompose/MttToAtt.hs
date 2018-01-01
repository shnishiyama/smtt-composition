{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.Decompose.MttToAtt where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import qualified Data.Tree.Trans.ATT        as ATT
import qualified Data.Tree.Trans.MAC        as MAC
import qualified Data.Tree.Trans.TOP        as TOP

data SubstitutionTreeF tb lb a
  = OriginalOutputLabelF lb
  | ContextParamF RankNumber
  | SubstitutionF (NodeVec a)
  deriving (Eq, Ord, Show, Generic, Generic1, Functor, Foldable)

instance (Hashable lb, Hashable a) => Hashable (SubstitutionTreeF tb lb a)

type instance Element (SubstitutionTreeF tb lb a) = a

instance MonoFoldable (SubstitutionTreeF tb lb a)

type SubstitutionTree tb lb = Fix (SubstitutionTreeF tb lb)

instance RtConstraint tb lb => RankedTree (Fix (SubstitutionTreeF tb lb)) where
  type LabelType (Fix (SubstitutionTreeF tb lb)) = SubstitutionTreeF tb lb ()

  treeLabel (Fix t) = void t
  treeChilds (Fix t) = fromList $ toList t

  treeLabelRank _ = length

  mkTreeUnchecked s cs = Fix $ case s of
    OriginalOutputLabelF l -> OriginalOutputLabelF l
    ContextParamF i        -> ContextParamF i
    SubstitutionF _        -> SubstitutionF cs

decomposeMtt :: forall s ta la tb lb.
  ( MAC.MttConstraint s ta la tb lb
  , Eq lb, Hashable lb
  )
  => MAC.MacroTreeTransducer s ta la tb lb
  -> (TOP.TdttTransducer s ta (SubstitutionTree tb lb), ATT.AttTransducer () RankNumber (SubstitutionTree tb lb) tb)
decomposeMtt trans =
    ( fromMaybe (error "unreachable") $ TOP.buildTdtt ie1 rules1
    , fromMaybe (error "unreachable") $ ATT.buildAtt ia2 irules2 rules2
    )
  where
    treeLabelRankTb = treeLabelRank (Proxy @tb)

    substitution cs = TOP.TdttLabelSide (SubstitutionF $ void cs) cs

    buildRhs xs (MAC.MttState s u cs) = let
        r = labelRank s
        (xs', cs') = undefined (r:xs, [] :: [Int])
      in (substitution $ fromList $ TOP.tdttState s u:cs', xs')
    buildRhs xs (MAC.MttContext c) = (TOP.TdttLabelSide (ContextParamF c) [], xs)
    buildRhs xs (MAC.MttLabelSide l cs) = let
        r = treeLabelRankTb l
        (xs', cs') = undefined (r:xs, [] :: [Int])
      in (substitution $ fromList $ TOP.TdttLabelSide (OriginalOutputLabelF l) []:cs', xs')

    (ie1, subs0) = buildRhs [] (MAC.mttInitialExpr trans)
    (rules1, subs1) = foldr
      (\((s, l), rhs) (xs, ys) -> let (rhs', ys') = buildRhs ys rhs in ((s, l, rhs'):xs, ys'))
      ([], subs0) $ mapToList $ MAC.mttTransRules trans

    ia2 = ()
    irules2 = undefined subs1
    rules2 = undefined
