{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.Decompose.MttToAtt where

import           SattPrelude

import           Control.Monad.State
import           Data.Tree.RankedTree
import qualified Data.Tree.Trans.ATT  as ATT
import qualified Data.Tree.Trans.MAC  as MAC
import qualified Data.Tree.Trans.TOP  as TOP
import qualified Data.Vector          as V

data SubstitutionTreeF tb lb a
  = OriginalOutputLabelF lb
  | ContextParamF RankNumber
  | SubstitutionF (NodeVec a)
  deriving (Eq, Ord, Show, Generic, Generic1, Functor, Foldable)

deriveEq1 ''SubstitutionTreeF
deriveOrd1 ''SubstitutionTreeF
deriveShow1 ''SubstitutionTreeF

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

-- | decompose a mtt to a tdtt and an att
--
-- Examples:
-- >>> import Data.Tree.RankedTree.Label
-- >>> import Data.Tree.Trans.MAC.Instances
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> (trans1, trans2) = decomposeMtt sampleMtt
-- >>> treeTrans trans2 <=< treeTrans trans1 $ inputSampleTree
-- D(F,F)
-- >>> (==) <$> (treeTrans trans2 <=< treeTrans trans1 $ inputSampleTree) <*> treeTrans sampleMtt inputSampleTree
-- True
--
decomposeMtt :: forall s ta la tb lb.
  ( MAC.MttConstraint s ta la tb lb
  , Eq lb, Hashable lb
  )
  => MAC.MacroTreeTransducer s ta la tb lb
  -> (TOP.TdttTransducer s ta (SubstitutionTree tb lb), ATT.AttTransducer () RankNumber (SubstitutionTree tb lb) tb)
decomposeMtt trans = fromMaybe (error "unreachable") $ (,)
    <$> TOP.buildTdtt ie1 rules1
    <*> ATT.buildAtt ia2 irules2 rules2
  where
    treeLabelRankTb = treeLabelRank (Proxy @tb)
    treeLabelRankSubst = treeLabelRank (Proxy @(SubstitutionTree tb lb))

    insertSubstLabel = modify' . first . insertSet
    updateMaxRank = modify' . second . max

    substitution i = SubstitutionF $ replicate (i + 1) ()

    buildRhs (MAC.MttState s u cs) = do
      let sub = substitution $ length cs
      insertSubstLabel sub
      updateMaxRank $ length cs
      cs' <- mapM buildRhs cs
      pure $ TOP.TdttLabelSide sub $ TOP.tdttState s u `cons` cs'
    buildRhs (MAC.MttContext c) = do
      let l' = ContextParamF c
      insertSubstLabel l'
      updateMaxRank $ c + 1
      pure $ TOP.TdttLabelSide l' []
    buildRhs (MAC.MttLabelSide l cs) = do
      let sub = substitution $ length cs
      let l' = OriginalOutputLabelF l
      insertSubstLabel sub
      insertSubstLabel l'
      updateMaxRank $ length cs
      cs' <- mapM buildRhs cs
      pure $ TOP.TdttLabelSide sub $ TOP.TdttLabelSide l' [] `cons` cs'

    ((ie1, rules1), (ls, mr)) = flip runState ([] :: HashSet (SubstitutionTreeF tb lb ()), 0) $ do
      ie <- buildRhs $ MAC.mttInitialExpr trans
      rules <- mapM (\((s, l), rhs) -> (s, l,) <$> buildRhs rhs) $ mapToList $ MAC.mttTransRules trans
      pure (ie, rules)

    ia2 = ()
    irules2 = (ATT.Synthesized (), ATT.SynAttrSide () 0):[]
    rules2
      =  [ (ATT.Synthesized (), l, h l) | l <- setToList ls ]
      <> do
        l <- setToList ls
        let p' = treeLabelRankSubst l
        when (p' == 0) empty
        let p = p' - 1

        j <- [0..(mr - 1)]
        i <- [0..p]

        pure
          ( ATT.Inherited (j, i), l
          , if i == 0 && j < p
            then ATT.SynAttrSide () $ j + 1
            else ATT.InhAttrSide j
          )

    h (OriginalOutputLabelF l) = ATT.AttLabelSide l $ V.generate (treeLabelRankTb l) ATT.InhAttrSide
    h (ContextParamF c)        = ATT.AttAttrSide $ ATT.Inherited c
    h SubstitutionF{}          = ATT.SynAttrSide () 0
