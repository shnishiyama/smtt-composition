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
  , BiRightHandSide
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

    -- standard form
  , toStandardForm

    -- reduction system
  , ReductionState
  , ReductionStateWithEmptySyn
  , buildSattReduction
  , runSattReduction
  , runSattReductionWithHistory
  , toInitialReductionState
  , fromReductionState
  , prettyShowReductionState

    -- internal
  , sattAttributes
  , sattInitialAttr
  , sattInitialRules
  , sattTransRules
  , sattInitialRule
  , sattTranslateRule
  , pattern SattLabelSideF
  , pattern SattStackBottomF
  , pattern SattStackHeadF
  , pattern SattAttrSideF
  , pattern SattStackEmptyF
  , pattern SattStackTailF
  , pattern SattStackConsF
  , prettyShowRhsValF
  , prettyShowRhsStkF
  , SattPathInfo
  , pattern SattPathInfo
  , sattPathList
  , sattNonPathZipper
  , sattIsInitial
  , emptySattPathInfo
  , zoomInIdxPathInfo
  ) where

import           SattPrelude

import           Data.Bifunctor.FixLR
import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Zipper
import           Data.Tree.Trans.ATT         (AttAttrEither (..), isInherited,
                                              isSynthesized)
import qualified Data.Tree.Trans.ATT         as ATT
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.Stack
import qualified Text.Show                   as S


type SattAttrEither = ATT.AttAttrEither

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


type RightHandSideVal syn inh t l = FixVal
  (RightHandSideValF syn inh t l ())
  (RightHandSideStkF syn inh t l ())

type RightHandSideStk syn inh t l = FixStk
  (RightHandSideValF syn inh t l ())
  (RightHandSideStkF syn inh t l ())

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

type BiRightHandSide syn inh t l = StackExprEither
  (RightHandSideVal syn inh t l)
  (RightHandSideStk syn inh t l)

instance (RtConstraint t l) => RankedTree (BiRightHandSide syn inh t l) where
  type LabelType (BiRightHandSide syn inh t l) = StackExprEither
    (RightHandSideValF syn inh t l () () ())
    (RightHandSideStkF syn inh t l () () ())

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
        SattStackConsF{}  -> BiFixStk $ SattStackConsF
          (fromValuedExpr $ cs `indexEx` 0)
          (fromStackedExpr $ cs `indexEx` 1)
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
  , sattInitialRules :: HashMap (SattAttrEither () inh) (RightHandSide syn inh tb lb)
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

coerceRhsStkInh :: forall syn inh tb lb. RightHandSideStk syn Void tb lb -> RightHandSideStk syn inh tb lb
coerceRhsStkInh (FixStk x) = FixStk $ case x of
  SattAttrSideF a () -> SattAttrSideF (second absurd a) ()
  SattStackEmptyF    -> SattStackEmptyF
  SattStackTailF s   -> SattStackTailF (coerceRhsStkInh s)
  SattStackConsF v s -> SattStackConsF (coerceRhsValInh v) (coerceRhsStkInh s)

coerceRhsValInh :: forall syn inh tb lb. RightHandSideVal syn Void tb lb -> RightHandSideVal syn inh tb lb
coerceRhsValInh (FixVal x) = FixVal $ case x of
  SattLabelSideF l cs -> SattLabelSideF l $ coerceRhsValInh <$> cs
  SattStackBottomF    -> SattStackBottomF
  SattStackHeadF s    -> SattStackHeadF (coerceRhsStkInh s)

buildSatt :: forall m syn inh ta la tb lb. (SattConstraint syn inh ta la tb lb, MonadThrow m)
  => syn
  -> [(SattAttrEither () inh, RightHandSide syn Void tb lb)]
  -> [(SattAttr syn inh, la, RightHandSide syn inh tb lb)]
  -> m (StackAttributedTreeTransducer syn inh ta la tb lb)
buildSatt ia irules rules = do
    let attrs0 = [Synthesized ia]
    (attrs1, irules') <- goInitial irules attrs0 []
    (attrs2, rules') <- go rules attrs1 []
    pure StackAttributedTreeTransducer
      { sattAttributes   = setFromList attrs2
      , sattInitialAttr  = ia
      , sattInitialRules = mapFromList irules'
      , sattTransRules   = mapFromList rules'
      }
  where
    treeLabelRankIn = treeLabelRank $ Proxy @ta
    treeLabelRankOut = treeLabelRank $ Proxy @tb

    goInitial []            xs ys = pure (xs, ys)
    goInitial ((a, rhs):rs) xs ys = do
      let rhs' = coerceRhsStkInh rhs
      let attrs = first (const ia) a:xs

      attrs' <- scanRHSStk 1 attrs rhs'

      let irule = (a, rhs')
      goInitial rs attrs' $ irule:ys

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

sattInitialRule :: SattConstraint syn inh ta la tb lb
  => StackAttributedTreeTransducer syn inh ta la tb lb
  -> SattAttrEither syn inh -> RightHandSide syn inh tb lb
sattInitialRule trans a = fromMaybe SattStackEmpty $ case a of
    Inherited   a' -> go $ Inherited a'
    Synthesized a' -> if a' == sattInitialAttr trans then go $ Synthesized () else Nothing
  where
    go attr = lookup attr $ sattInitialRules trans

sattTranslateRule :: SattConstraint syn inh ta la tb lb
  => StackAttributedTreeTransducer syn inh ta la tb lb
  -> SattAttr syn inh -> la -> RightHandSide syn inh tb lb
sattTranslateRule trans a l = fromMaybe SattStackEmpty $ lookup (a, l) $ sattTransRules trans


-- reduction system

type SattPathInfo = ATT.AttPathInfo

pattern SattPathInfo :: [RankNumber] -> tz t l -> Bool -> SattPathInfo tz t l
pattern SattPathInfo{sattPathList,sattNonPathZipper,sattIsInitial} = ATT.AttPathInfo
  { ATT.attPathList      = sattPathList
  , ATT.attNonPathZipper = sattNonPathZipper
  , ATT.attIsInitial     = sattIsInitial
  }

{-# COMPLETE SattPathInfo #-}

emptySattPathInfo :: forall tz t l. (RtConstraint t l, RankedTreeZipper tz)
  => Bool -> t -> SattPathInfo tz t l
emptySattPathInfo = ATT.emptyAttPathInfo

emptySattPathInfoFromZipper :: forall tz t l. (RtConstraint t l, RankedTreeZipper tz)
  => Bool -> tz t l -> SattPathInfo tz t l
emptySattPathInfoFromZipper = ATT.emptyAttPathInfoFromZipper

zoomInIdxPathInfo :: (RankedTreeZipper tz, RtConstraint t l)
  => RankNumber -> SattPathInfo tz t l -> Maybe (SattPathInfo tz t l)
zoomInIdxPathInfo = ATT.zoomInIdxPathInfo

type ReductionState syn inh ta la tb lb tz = BiStackExprFix
  (RightHandSideValF syn inh tb lb (SattPathInfo tz ta la))
  (RightHandSideStkF syn inh tb lb (SattPathInfo tz ta la))

pattern RedFixVal
  :: BiStackExprFixVal
    (RightHandSideValF syn inh tb lb (SattPathInfo tz ta la))
    (RightHandSideStkF syn inh tb lb (SattPathInfo tz ta la))
  -> ReductionState syn inh ta la tb lb tz
pattern RedFixVal s = BiFixVal s

pattern RedFixStk
  :: BiStackExprFixStk
    (RightHandSideValF syn inh tb lb (SattPathInfo tz ta la))
    (RightHandSideStkF syn inh tb lb (SattPathInfo tz ta la))
  -> ReductionState syn inh ta la tb lb tz
pattern RedFixStk s = BiFixStk s

{-# COMPLETE RedFixVal, RedFixStk #-}

type ReductionStateValF syn inh ta la tb lb tz val stk
  = RightHandSideValF syn inh tb lb (SattPathInfo tz ta la) val stk

type ReductionStateStkF syn inh ta la tb lb tz val stk
  = RightHandSideStkF syn inh tb lb (SattPathInfo tz ta la) val stk

instance (SattConstraint syn inh ta la tb lb) => RankedTree (ReductionState syn inh ta la tb lb tz) where
  type LabelType (ReductionState syn inh ta la tb lb tz) = StackExprEither
    (ReductionStateValF syn inh ta la tb lb tz () ())
    (ReductionStateStkF syn inh ta la tb lb tz () ())

  treeLabel (RedFixVal x) = ValuedExpr  $ bivoid x
  treeLabel (RedFixStk x) = StackedExpr $ bivoid x

  treeChilds (RedFixVal x) = fromList $ biList $ bimap ValuedExpr StackedExpr x
  treeChilds (RedFixStk x) = fromList $ biList $ bimap ValuedExpr StackedExpr x

  treeLabelRank _ (ValuedExpr  x) = bilength x
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
        SattStackConsF{}  -> BiFixStk $ SattStackConsF
          (fromValuedExpr $ cs `indexEx` 0)
          (fromStackedExpr $ cs `indexEx` 1)
    where
      fromValuedExpr (ValuedExpr x) = x
      fromValuedExpr _              = error "expected a valued expression"

      fromStackedExpr (StackedExpr x) = x
      fromStackedExpr _               = error "expected a stacked expression"

type ReductionStateWithEmptySyn syn inh ta la tb lb tz
  = Either (Bool, tz ta la, syn) (ReductionState syn inh ta la tb lb tz)

buildSattReduction :: forall tz b syn inh ta la tb lb.
  (SattConstraint syn inh ta la tb lb, RankedTreeZipper tz)
  => (RtApply tz (ReductionState syn inh ta la tb lb tz) -> b -> b) -> b
  -> StackAttributedTreeTransducer syn inh ta la tb lb
  -> ReductionStateWithEmptySyn syn inh ta la tb lb tz
  -> b
buildSattReduction f is trans mt = go is' initialZipper
  where
    (initialZipper, is') = case mt of
      Left (b, tz, a) -> let
          !sz   = toZipper $ toRedState b tz a
          !nis = f sz is
        in (sz, nis)
      Right s         -> (toZipper s, is)

    initialRule = sattInitialRule trans
    rule = sattTranslateRule trans

    toRedState True  tz a = toRedState' True  tz $ initialRule (Synthesized a)
    toRedState False tz a = toRedState' False tz $ rule (Synthesized a) (toTreeLabel tz)

    toRedState' b tz = RedFixVal . SattStackHeadF
      . replaceRHSStk (emptySattPathInfoFromZipper b tz)

    checkReducible (RedFixVal x) = case x of
      SattLabelSideF{}   -> False
      SattStackBottomF{} -> False
      SattStackHeadF{}   -> False
    checkReducible (RedFixStk x) = case x of
      SattAttrSideF Inherited{} SattPathInfo{ sattPathList = [] } -> False
      SattAttrSideF{}                                             -> True
      SattStackEmptyF{}                                           -> False
      SattStackTailF{}                                            -> False
      SattStackConsF{}                                            -> True

    go x sz = case zoomNextRightOutZipper (checkReducible . toTree) sz of
      Just sz' -> let
          !nsz = reductState sz'
          !nx = f nsz x
        in go nx nsz
      Nothing -> x

    reductState sz = case toTree sz of
      RedFixStk x -> case x of
        SattAttrSideF a p  -> setTreeZipper (reductAttrSide a p) sz
        SattStackConsF h t -> deconsStackCons h t sz
        _                  -> error "This state is irreducible"
      RedFixVal _ -> error "This state is irreducible"

    reductAttrSide (Synthesized (a, i)) p = case zoomInIdxPathInfo i p of
      Nothing -> error "Using an over indexed synthesized attribute"
      Just np -> replaceRHS np $ rule (Synthesized a) (toTreeLabel np)
    reductAttrSide (Inherited a) (SattPathInfo (i:pl) z False) = case zoomOutRtZipper z of
      Nothing -> replaceRHS (SattPathInfo pl z  True)  $ initialRule (Inherited a)
      Just z' -> replaceRHS (SattPathInfo pl z' False) $ rule (Inherited (a, i)) (toTreeLabel z')
    reductAttrSide Inherited{} SattPathInfo{} = error "This state is irreducible"

    deconsStackCons h t sz = case zoomOutRtZipper sz of
      Nothing  -> errorUnreachable
      Just nsz -> case toTree nsz of
        RedFixVal x -> case x of
          SattStackHeadF{} -> setTreeZipper (ValuedExpr h) nsz
          _                -> errorUnreachable
        RedFixStk x -> case x of
          SattStackTailF{} -> setTreeZipper (StackedExpr t) nsz
          _                -> errorUnreachable

    replaceRHS p = StackedExpr . replaceRHSStk p

    replaceRHSVal p (FixVal x) = FixVal $ case x of
      SattLabelSideF l cs -> SattLabelSideF l $ replaceRHSVal p <$> cs
      SattStackBottomF    -> SattStackBottomF
      SattStackHeadF s    -> SattStackHeadF $ replaceRHSStk p s

    replaceRHSStk p (FixStk x) = FixStk $ case x of
      SattAttrSideF a _    -> SattAttrSideF a p
      SattStackEmptyF      -> SattStackEmptyF
      SattStackTailF s     -> SattStackTailF $ replaceRHSStk p s
      SattStackConsF v s   -> SattStackConsF
        (replaceRHSVal p v)
        (replaceRHSStk p s)

runSattReduction :: forall tz syn inh ta la tb lb.
  ( SattConstraint syn inh ta la tb lb, RankedTreeZipper tz
  )
  => StackAttributedTreeTransducer syn inh ta la tb lb
  -> ReductionStateWithEmptySyn syn inh ta la tb lb tz
  -> ReductionState syn inh ta la tb lb tz
runSattReduction trans istate = toTopTree
  $ buildSattReduction const (either (const errorUnreachable) toZipper istate) trans istate

runSattReductionWithHistory :: forall tz syn inh ta la tb lb.
  ( SattConstraint syn inh ta la tb lb, RankedTreeZipper tz
  )
  => StackAttributedTreeTransducer syn inh ta la tb lb
  -> ReductionStateWithEmptySyn syn inh ta la tb lb tz
  -> [ReductionState syn inh ta la tb lb tz]
runSattReductionWithHistory trans istate
  = buildSattReduction (\tz -> (. (toTopTree tz:))) id trans istate []

toInitialReductionState :: forall tz syn inh ta la tb lb.
  ( SattConstraint syn inh ta la tb lb, RankedTreeZipper tz
  )
  => StackAttributedTreeTransducer syn inh ta la tb lb
  -> ta -> ReductionStateWithEmptySyn syn inh ta la tb lb tz
toInitialReductionState trans t = Left (True, toZipper t, sattInitialAttr trans)

fromReductionState ::
  ( SattConstraint syn inh ta la tb lb, RankedTreeZipper tz
  )
  => ReductionState syn inh ta la tb lb tz -> Maybe tb
fromReductionState x = case x of
    ValuedExpr  x' -> fromReductionStateVal x'
    StackedExpr x' -> fromReductionStateStk x'
  where
    fromReductionStateVal (FixVal x') = case x' of
      SattLabelSideF l cs  -> do
        cs' <- mapM fromReductionStateVal cs
        pure $ mkTreeUnchecked l cs'
      SattStackBottomF    -> pure $ mkTreeUnchecked bottomLabel []
      _                   -> Nothing

    fromReductionStateStk (FixStk x') = case x' of
      _ -> Nothing

prettyShowReductionState ::
  ( Show syn, Show inh, Show la, Show lb
  , RtConstraint ta la, RtConstraint tb lb
  , RankedTreeZipper tz
  )
  => ReductionState syn inh ta la tb lb tz -> String
prettyShowReductionState state = go state ""
  where
    go (ValuedExpr  x) = goVal x
    go (StackedExpr x) = goStk x

    goVal (FixVal x) = prettyShowRhsValF attrShow' goVal goStk x
    goStk (FixStk x) = prettyShowRhsStkF attrShow' goVal goStk x

    attrShow' (a, SattPathInfo pl mz b) = attrShow a pl mz b

    attrShow a pl z b = let lShow = labelShow z b in case a of
      Synthesized (a', i) -> S.shows a' . S.shows (i:pl) . S.showString "(" . lShow . S.showString ")"
      Inherited   a'      -> S.shows a' . S.shows pl . S.showString "(" . lShow . S.showString ")"

    labelShow _ True  = S.showString "#"
    labelShow z False = S.shows $ toTreeLabel z


-- A tree transduction for satts
instance SattConstraint syn inh ta la tb lb
    => TreeTransducer (StackAttributedTreeTransducer syn inh ta la tb lb) ta tb where

  treeTrans trans
    =   (toInitialReductionState @RTZipper trans)
    >>> runSattReduction trans
    >>> fromReductionState
    >>> maybe (throwErrorM "This tree transducer is illegal.") pure


-- standard form

toStandardForm :: SattConstraint syn inh ta la tb lb
  => StackAttributedTreeTransducer syn inh ta la tb lb
  -> StackAttributedTreeTransducer syn inh ta la tb lb
toStandardForm trans = trans
    { sattInitialRules = initialRules
    , sattTransRules   = rules
    }
  where
    initialRules = evalStackStkExpr <$> sattInitialRules trans

    rules = evalStackStkExpr <$> sattTransRules trans
