{-# LANGUAGE NoStrict        #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.SATT
  ( -- common
    StackAttributedTreeTransducer
  , SattTransducer
  , SattConstraint
  , buildSatt
  , SattAttrDepend
  , SattAttr
  , RightHandSide
  , pattern SattAttrSide
  , pattern SynAttrSide
  , pattern InhAttrSide
  , pattern SattLabelSide
  , pattern SattStackBottom
  , pattern SattStackHead
  , pattern SattStackTail
  , pattern SattStackEmpty
  , pattern SattStackCons
  , prettyShowRhs

    -- either utility
  , SattAttrEither
  , AttAttrEither (..)
  , isSynthesized
  , isInherited

    -- internal
  , coerceRhsInh
  , coerceRhsInh1
  ) where

import           SattPrelude

import           Data.Bifunctor.FixLR
import           Data.Tree.RankedTree
import           Data.Tree.Trans.ATT   (AttAttrEither (..), isInherited,
                                        isSynthesized)
import           Data.Tree.Trans.Stack
import qualified Text.Show             as S
import qualified Unsafe.Coerce         as Unsafe


type SattAttrEither = AttAttrEither

type SattAttrDepend syn inh = SattAttrEither
  (syn, RankNumber)
  inh

data BaseRightHandSideValF syn inh t l pi valrhs stkrhs
  = BaseSattLabelSideF l (NodeVec valrhs)
  deriving (Eq, Ord, Show, Generic)

instance (Hashable syn, Hashable inh, Hashable l, Hashable pi, Hashable valrhs, Hashable stkrhs)
  => Hashable (BaseRightHandSideValF syn inh t l pi valrhs stkrhs)

deriveEq2 ''BaseRightHandSideValF
deriveOrd2 ''BaseRightHandSideValF
deriveShow2 ''BaseRightHandSideValF
deriveBifunctor ''BaseRightHandSideValF
deriveBifoldable ''BaseRightHandSideValF

type RightHandSideValF syn inh t l pi = BaseRightHandSideValF syn inh t l pi :+|+: StackExprValF

pattern SattLabelSideF :: l -> NodeVec valrhs -> RightHandSideValF syn inh t l pi valrhs stkrhs
pattern SattLabelSideF l cs = BiInL (BaseSattLabelSideF l cs)

pattern SattStackBottomF :: RightHandSideValF syn inh t l pi valrhs stkrhs
pattern SattStackBottomF = BiInR StackBottomF

pattern SattStackHeadF :: stkrhs -> RightHandSideValF syn inh t l pi valrhs stkrhs
pattern SattStackHeadF s = BiInR (StackHeadF s)

{-# COMPLETE SattLabelSideF, SattStackBottomF, SattStackHeadF #-}

data BaseRightHandSideStkF syn inh t l pi valrhs stkrhs
  = BaseSattAttrSideF (SattAttrDepend syn inh) pi
  deriving (Eq, Ord, Show, Generic)

instance (Hashable syn, Hashable inh, Hashable l, Hashable pi, Hashable valrhs, Hashable stkrhs)
  => Hashable (BaseRightHandSideStkF syn inh t l pi valrhs stkrhs)

deriveEq2 ''BaseRightHandSideStkF
deriveOrd2 ''BaseRightHandSideStkF
deriveShow2 ''BaseRightHandSideStkF
deriveBifunctor ''BaseRightHandSideStkF
deriveBifoldable ''BaseRightHandSideStkF

type RightHandSideStkF syn inh t l pi = BaseRightHandSideStkF syn inh t l pi :+|+: StackExprStkF

pattern SattAttrSideF :: SattAttrDepend syn inh -> pi -> RightHandSideStkF syn inh t l pi valrhs stkrhs
pattern SattAttrSideF a p = BiInL (BaseSattAttrSideF a p)

pattern SattStackEmptyF :: RightHandSideStkF syn inh t l pi valrhs stkrhs
pattern SattStackEmptyF = BiInR StackEmptyF

pattern SattStackTailF :: stkrhs -> RightHandSideStkF syn inh t l pi valrhs stkrhs
pattern SattStackTailF s = BiInR (StackTailF s)

pattern SattStackConsF :: valrhs -> stkrhs -> RightHandSideStkF syn inh t l pi valrhs stkrhs
pattern SattStackConsF v s = BiInR (StackConsF v s)

{-# COMPLETE SattAttrSideF, SattStackEmptyF, SattStackTailF, SattStackConsF #-}

prettyShowRhsValF :: (Show l, RtConstraint t l)
  => ((SattAttrDepend syn inh, pi) -> S.ShowS)
  -> (valrhs -> S.ShowS) -> (stkrhs -> S.ShowS)
  -> RightHandSideValF syn inh t l pi valrhs stkrhs
  -> S.ShowS
prettyShowRhsValF _ vrhsShow srhsShow x = case x of
  SattLabelSideF l cs -> S.shows l . S.showString "(" . foldl' (.) id (intersperse (S.showString ", ") $ vrhsShow <$> cs) . S.showString ")"
  SattStackBottomF    -> S.showString "_|_"
  SattStackHeadF s    -> S.showString "Head(" . srhsShow s . S.showString ")"

prettyShowRhsStkF :: (Show l, RtConstraint t l)
  => ((SattAttrDepend syn inh, pi) -> S.ShowS)
  -> (valrhs -> S.ShowS) -> (stkrhs -> S.ShowS)
  -> RightHandSideStkF syn inh t l pi valrhs stkrhs
  -> S.ShowS
prettyShowRhsStkF attrShow vrhsShow srhsShow x = case x of
  SattAttrSideF a p  -> attrShow (a, p)
  SattStackEmptyF    -> S.showString "Empty"
  SattStackTailF s   -> S.showString "Tail(" . srhsShow s . S.showString ")"
  SattStackConsF v s -> S.showString "Cons(" . vrhsShow v . S.showString ", " . srhsShow s . S.showString ")"


type RightHandSideVal syn inh t l = FixVal (RightHandSideValF syn inh t l ()) (RightHandSideStkF syn inh t l ())

type RightHandSideStk syn inh t l = FixStk (RightHandSideValF syn inh t l ()) (RightHandSideStkF syn inh t l ())

type RightHandSide syn inh t l = RightHandSideStk syn inh t l

pattern SattAttrSide :: RtConstraint t l
  => SattAttrDepend syn inh -> RightHandSideStk syn inh t l
pattern SattAttrSide a = FixStk (SattAttrSideF a ())

pattern SynAttrSide :: RtConstraint t l
  => syn -> RankNumber -> RightHandSideStk syn inh t l
pattern SynAttrSide a i = SattAttrSide (Synthesized (a, i))

pattern InhAttrSide :: RtConstraint t l
  => inh -> RightHandSideStk syn inh t l
pattern InhAttrSide a = SattAttrSide (Inherited a)

pattern SattLabelSide :: RtConstraint t l
  => l -> NodeVec (RightHandSideVal syn inh t l) -> RightHandSideVal syn inh t l
pattern SattLabelSide l cs = FixVal (SattLabelSideF l cs)

pattern SattStackBottom :: RtConstraint t l
  => RightHandSideVal syn inh t l
pattern SattStackBottom = FixVal SattStackBottomF

pattern SattStackHead :: RtConstraint t l
  => RightHandSideStk syn inh t l -> RightHandSideVal syn inh t l
pattern SattStackHead s = FixVal (SattStackHeadF s)

pattern SattStackEmpty :: RtConstraint t l
  => RightHandSideStk syn inh t l
pattern SattStackEmpty = FixStk SattStackEmptyF

pattern SattStackTail :: RtConstraint t l
  => RightHandSideStk syn inh t l -> RightHandSideStk syn inh t l
pattern SattStackTail s = FixStk (SattStackTailF s)

pattern SattStackCons :: RtConstraint t l
  => RightHandSideVal syn inh t l -> RightHandSideStk syn inh t l -> RightHandSideStk syn inh t l
pattern SattStackCons v s = FixStk (SattStackConsF v s)

{-# COMPLETE SattLabelSide, SattStackBottom, SattStackHead #-}
{-# COMPLETE SattAttrSide, SattStackEmpty, SattStackTail, SattStackCons #-}
{-# COMPLETE SynAttrSide, InhAttrSide, SattStackEmpty, SattStackTail, SattStackCons #-}

instance (RtConstraint t l) => RankedTree (StackExprEither (RightHandSideVal syn inh t l) (RightHandSideStk syn inh t l)) where
  type LabelType (StackExprEither (RightHandSideVal syn inh t l) (RightHandSideStk syn inh t l)) = StackExprEither (RightHandSideValF syn inh t l () () ()) (RightHandSideStkF syn inh t l () () ())

  treeLabel (BiFixVal x) = ValuedExpr  $ bivoid x
  treeLabel (BiFixStk x) = StackedExpr $ bivoid x

  treeChilds (BiFixVal x) = fromList $ biList $ bimap ValuedExpr StackedExpr x
  treeChilds (BiFixStk x) = fromList $ biList $ bimap ValuedExpr StackedExpr x

  treeLabelRank _ (ValuedExpr x)  = bilength x
  treeLabelRank _ (StackedExpr x) = bilength x

  mkTreeUnchecked e cs = case e of
      ValuedExpr ve -> case ve of
        SattLabelSideF l _ -> BiFixVal $ SattLabelSideF l $ fromValuedExpr <$> cs
        SattStackBottomF   -> BiFixVal SattStackBottomF
        SattStackHeadF{}   -> BiFixVal $ SattStackHeadF (fromStackedExpr $ cs `indexEx` 0)
      StackedExpr se -> case se of
        SattAttrSideF a p -> BiFixStk $ SattAttrSideF a p
        SattStackEmptyF   -> BiFixStk SattStackEmptyF
        SattStackTailF{}  -> BiFixStk $ SattStackTailF (fromStackedExpr $ cs `indexEx` 0)
        SattStackConsF{}  -> BiFixStk $ SattStackConsF (fromValuedExpr $ cs `indexEx` 0) (fromStackedExpr $ cs `indexEx` 1)
    where
      fromValuedExpr (ValuedExpr x) = x
      fromValuedExpr _              = error "expected a valued expression"

      fromStackedExpr (StackedExpr x) = x
      fromStackedExpr _               = error "expected a stacked expression"

prettyShowRhs :: (Show syn, Show inh, Show l, RtConstraint t l)
  => RightHandSide syn inh t l -> String
prettyShowRhs rhs = goStk rhs ""
  where
    goStk (FixStk x) = prettyShowRhsStkF attrShow' goVal goStk x
    goVal (FixVal x) = prettyShowRhsValF attrShow' goVal goStk x

    attrShow' (a, ()) = attrShow a

    attrShow (Synthesized (a, i)) = S.shows a . S.showString "[" . S.shows i . S.showString ", ...]"
    attrShow (Inherited a)        = S.shows a . S.showString "[...]"

type SattAttr syn inh = SattAttrEither
  syn
  (inh, RankNumber)

data StackAttributedTreeTransducer syn inh ta la tb lb = StackAttributedTreeTransducer
  { sattAttributes   :: HashSet (SattAttrEither syn inh)
  , sattInitialAttr  :: syn
  , sattInitialRules :: HashMap (SattAttrEither () inh) (RightHandSide syn Void tb lb)
  , sattTransRules   :: HashMap (SattAttr syn inh, la) (RightHandSide syn inh tb lb)
  } deriving (Eq, Generic)

type SattTransducer syn inh ta tb
  = StackAttributedTreeTransducer syn inh ta (LabelType ta) tb (LabelType tb)

type SattConstraint syn inh ta la tb lb =
  ( RtConstraint ta la
  , RtConstraint tb lb
  , Eq syn, Hashable syn
  , Eq inh, Hashable inh
  , Eq la, Hashable la
  )

instance (Show syn, Show inh, Show la, Show lb, SattConstraint syn inh ta la tb lb)
    => Show (StackAttributedTreeTransducer syn inh ta la tb lb) where

  show StackAttributedTreeTransducer{..} = "StackAttributedTreeTransducer{"
      <> " sattAttributes = " <> show (toList sattAttributes) <> ","
      <> " sattInitialAttr = " <> show sattInitialAttr <> ","
      <> " sattTranslateRules = [" <> intercalate ", "
        (  (showInitialRule <$> mapToList sattInitialRules)
        <> (showRule <$> mapToList sattTransRules)
        )
      <> "],"
      <> " }"
    where
      showInitialRule (a, rhs) = showRule' "#" (bimap id (,0 :: RankNumber) a) rhs

      showRule ((a, l), rhs) = showRule' (show l) a rhs

      showRule' lshow a rhs
        = attrShow a
        <> " -(" <> lshow <> ")-> "
        <> prettyShowRhs rhs

      attrShow (Synthesized a)    = show a <> "[...]"
      attrShow (Inherited (a, i)) = show a <> "[" <> show i <> ", ...]"

-- FIXME: Maybe this coerce raise core lint warnings
coerceRhsInh :: RightHandSide syn Void tb lb -> RightHandSide syn inh tb lb
coerceRhsInh = Unsafe.unsafeCoerce

-- FIXME: Maybe this coerce raise core lint warnings
coerceRhsInh1 :: Functor f => f (RightHandSide syn Void tb lb) -> f (RightHandSide syn inh tb lb)
coerceRhsInh1 = Unsafe.unsafeCoerce

buildSatt :: forall m syn inh ta la tb lb. (SattConstraint syn inh ta la tb lb, MonadThrow m)
  => syn
  -> [(SattAttrEither () inh, RightHandSide syn Void tb lb)]
  -> [(SattAttr syn inh, la, RightHandSide syn inh tb lb)]
  -> m (StackAttributedTreeTransducer syn inh ta la tb lb)
buildSatt ia irules rules = do
    let attrs0 = [Synthesized ia]
    attrs1 <- foldM
      (\attrs (a, rhs) -> scanRHSStk 1 (first (const ia) a:attrs) $ coerceRhsInh rhs)
      attrs0 irules
    (attrs2, rules') <- go rules attrs1 []
    pure StackAttributedTreeTransducer
      { sattAttributes   = setFromList attrs2
      , sattInitialAttr  = ia
      , sattInitialRules = mapFromList irules
      , sattTransRules   = mapFromList rules'
      }
  where
    treeLabelRankIn = treeLabelRank $ Proxy @ta
    treeLabelRankOut = treeLabelRank $ Proxy @tb

    go [] xs ys             = pure (xs, ys)
    go ((a,l,rhs):rs) xs ys = do
      let k = treeLabelRankIn l
      attrs' <- checkAttr a k xs

      attrs'' <- scanRHSStk k attrs' rhs

      let rule = ((a, l), rhs)
      go rs attrs'' $ rule:ys

    checkAttr (Synthesized a)    _ xs = pure $ Synthesized a:xs
    checkAttr (Inherited (a, i)) k xs
      | i < k     = pure $ Inherited a:xs
      | otherwise = throwErrorM "Using an over indexed inherited attribute"

    scanRHSStk k xs (FixStk rhs) = case rhs of
      SattAttrSideF (Synthesized (a, i)) () -> if i < k
        then pure $ Synthesized a:xs
        else throwErrorM "Using an over indexed synthesized attribute"
      SattAttrSideF (Inherited a) () -> pure $ Inherited a:xs
      SattStackEmptyF  -> pure xs
      SattStackTailF s -> scanRHSStk k xs s
      SattStackConsF v s -> do
        xs' <- scanRHSVal k xs v
        scanRHSStk k xs' s

    scanRHSVal k xs (FixVal rhs) = case rhs of
      SattStackBottomF -> pure xs
      SattStackHeadF s -> scanRHSStk k xs s
      SattLabelSideF l cs -> if length cs == treeLabelRankOut l
        then foldM (scanRHSVal k) xs cs
        else throwErrorM "Mismatch the rank of an output label for childs"
