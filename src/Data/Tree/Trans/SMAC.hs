{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.SMAC
  ( -- common
    StackMacroTreeTransducer
  , SmttTransducer
  , SmttConstraint
  , buildSmtt
  , RightHandSide
  , BiRightHandSide
  , pattern SmttContext
  , pattern SmttState
  , pattern SmttLabelSide
  , pattern SmttStackBottom
  , pattern SmttStackHead
  , pattern SmttStackTail
  , pattern SmttStackEmpty
  , pattern SmttStackCons
  , prettyShowRhs

  ) where

import SattPrelude

import qualified Text.Show as S
import Data.Tree.RankedTree
import Data.Tree.Trans.Stack
import Data.Bifunctor.FixLR
import Data.Tree.RankedTree.Label


data BaseRightHandSideValF s t l u c valrhs stkrhs
  = BaseSmttLabelSideF l (NodeVec valrhs)
  deriving (Eq, Ord, Show, Generic)

instance (Hashable s, Hashable l, Hashable valrhs, Hashable stkrhs)
  => Hashable (BaseRightHandSideValF s t l u c valrhs stkrhs)

deriveEq2 ''BaseRightHandSideValF
deriveOrd2 ''BaseRightHandSideValF
deriveShow2 ''BaseRightHandSideValF
deriveBifunctor ''BaseRightHandSideValF
deriveBifoldable ''BaseRightHandSideValF

type RightHandSideValF s t l u c = BaseRightHandSideValF s t l u c :+|+: StackExprValF

pattern SmttLabelSideF :: l -> NodeVec valrhs -> RightHandSideValF s t l u c valrhs stkrhs
pattern SmttLabelSideF l cs = BiInL (BaseSmttLabelSideF l cs)

pattern SmttStackBottomF :: RightHandSideValF s t l u c valrhs stkrhs
pattern SmttStackBottomF = BiInR StackBottomF

pattern SmttStackHeadF :: stkrhs -> RightHandSideValF s t l u c valrhs stkrhs
pattern SmttStackHeadF s = BiInR (StackHeadF s)

{-# COMPLETE SmttLabelSideF, SmttStackBottomF, SmttStackHeadF #-}

data BaseRightHandSideStkF s t l u c valrhs stkrhs
  = BaseSmttContextF c
  | BaseSmttStateF s u (NodeVec stkrhs)
  deriving (Eq, Ord, Show, Generic)

instance (Hashable s, Hashable u, Hashable c, Hashable valrhs, Hashable stkrhs)
  => Hashable (BaseRightHandSideStkF s t l u c valrhs stkrhs)

deriveEq2 ''BaseRightHandSideStkF
deriveOrd2 ''BaseRightHandSideStkF
deriveShow2 ''BaseRightHandSideStkF
deriveBifunctor ''BaseRightHandSideStkF
deriveBifoldable ''BaseRightHandSideStkF

type RightHandSideStkF s t l u c = BaseRightHandSideStkF s t l u c :+|+: StackExprStkF

pattern SmttContextF :: c -> RightHandSideStkF s t l u c valrhs stkrhs
pattern SmttContextF c = BiInL (BaseSmttContextF c)

pattern SmttStateF :: s -> u -> NodeVec stkrhs -> RightHandSideStkF s t l u c valrhs stkrhs
pattern SmttStateF s u cs = BiInL (BaseSmttStateF s u cs)

pattern SmttStackEmptyF :: RightHandSideStkF s t l u c valrhs stkrhs
pattern SmttStackEmptyF = BiInR StackEmptyF

pattern SmttStackTailF :: stkrhs -> RightHandSideStkF s t l u c valrhs stkrhs
pattern SmttStackTailF s = BiInR (StackTailF s)

pattern SmttStackConsF :: valrhs -> stkrhs -> RightHandSideStkF s t l u c valrhs stkrhs
pattern SmttStackConsF v s = BiInR (StackConsF v s)

{-# COMPLETE SmttContextF, SmttStateF, SmttStackEmptyF, SmttStackTailF, SmttStackConsF #-}

prettyShowRhsValF :: (Show s, Show l)
  => (u -> S.ShowS) -> (c -> S.ShowS)
  -> (valrhs -> S.ShowS) -> (stkrhs -> S.ShowS)
  -> RightHandSideValF s t l u c valrhs stkrhs
  -> S.ShowS
prettyShowRhsValF _ _ vrhsShow srhsShow x = case x of
  SmttLabelSideF l cs -> S.shows l . S.showString "(" . foldl' (.) id (intersperse (S.showString ", ") $ vrhsShow <$> cs) . S.showString ")"
  SmttStackBottomF    -> S.showString "_|_"
  SmttStackHeadF s    -> S.showString "Head(" . srhsShow s . S.showString ")"

prettyShowRhsStkF :: (Show s, Show l)
  => (u -> S.ShowS) -> (c -> S.ShowS)
  -> (valrhs -> S.ShowS) -> (stkrhs -> S.ShowS)
  -> RightHandSideStkF s t l u c valrhs stkrhs
  -> S.ShowS
prettyShowRhsStkF uShow cShow vrhsShow srhsShow x = case x of
  SmttContextF c  -> cShow c
  SmttStateF s u cs -> S.shows s . S.showString "(" . uShow u
    . foldl' (.) id (cs <&> \rhs -> S.showString "," . srhsShow rhs) . S.showString ")"
  SmttStackEmptyF    -> S.showString "Empty"
  SmttStackTailF s   -> S.showString "Tail(" . srhsShow s . S.showString ")"
  SmttStackConsF v s -> S.showString "Cons(" . vrhsShow v . S.showString ", " . srhsShow s . S.showString ")"


type RightHandSideVal s t l = FixVal
  (RightHandSideValF s t l RankNumber RankNumber)
  (RightHandSideStkF s t l RankNumber RankNumber)

type RightHandSideStk s t l = FixStk
  (RightHandSideValF s t l RankNumber RankNumber)
  (RightHandSideStkF s t l RankNumber RankNumber)

type RightHandSide s t l = RightHandSideStk s t l

pattern SmttContext :: RankNumber -> RightHandSideStk s t l
pattern SmttContext c = FixStk (SmttContextF c)

pattern SmttState :: s -> RankNumber -> NodeVec (RightHandSideStk s t l) -> RightHandSideStk s t l
pattern SmttState s t cs = FixStk (SmttStateF s t cs)

pattern SmttLabelSide :: l -> NodeVec (RightHandSideVal s t l) -> RightHandSideVal s t l
pattern SmttLabelSide l cs = FixVal (SmttLabelSideF l cs)

pattern SmttStackBottom :: RightHandSideVal s t l
pattern SmttStackBottom = FixVal SmttStackBottomF

pattern SmttStackHead :: RightHandSideStk s t l -> RightHandSideVal s t l
pattern SmttStackHead s = FixVal (SmttStackHeadF s)

pattern SmttStackEmpty :: RightHandSideStk s t l
pattern SmttStackEmpty = FixStk SmttStackEmptyF

pattern SmttStackTail :: RightHandSideStk s t l -> RightHandSideStk s t l
pattern SmttStackTail s = FixStk (SmttStackTailF s)

pattern SmttStackCons :: RightHandSideVal s t l -> RightHandSideStk s t l -> RightHandSideStk s t l
pattern SmttStackCons v s = FixStk (SmttStackConsF v s)

{-# COMPLETE SmttLabelSide, SmttStackBottom, SmttStackHead #-}
{-# COMPLETE SmttContext, SmttState, SmttStackEmpty, SmttStackTail, SmttStackCons #-}

type BiRightHandSide s t l = StackExprEither
  (RightHandSideVal s t l)
  (RightHandSideStk s t l)

instance (RtConstraint t l) => RankedTree (BiRightHandSide s t l) where
  type LabelType (BiRightHandSide s t l) = StackExprEither
    (RightHandSideValF s t l RankNumber RankNumber () ())
    (RightHandSideStkF s t l RankNumber RankNumber () ())

  treeLabel (BiFixVal x) = ValuedExpr  $ bivoid x
  treeLabel (BiFixStk x) = StackedExpr $ bivoid x

  treeChilds (BiFixVal x) = fromList $ biList $ bimap ValuedExpr StackedExpr x
  treeChilds (BiFixStk x) = fromList $ biList $ bimap ValuedExpr StackedExpr x

  treeLabelRank _ (ValuedExpr x)  = bilength x
  treeLabelRank _ (StackedExpr x) = bilength x

  mkTreeUnchecked e cs = case e of
      ValuedExpr ve -> case ve of
        SmttLabelSideF l _ -> BiFixVal $ SmttLabelSideF l $ fromValuedExpr <$> cs
        SmttStackBottomF   -> BiFixVal SmttStackBottomF
        SmttStackHeadF{}   -> BiFixVal $ SmttStackHeadF (fromStackedExpr $ cs `indexEx` 0)
      StackedExpr se -> case se of
        SmttContextF c -> BiFixStk $ SmttContextF c
        SmttStateF s u _ -> BiFixStk $ SmttStateF s u $ fromStackedExpr <$> cs
        SmttStackEmptyF   -> BiFixStk SmttStackEmptyF
        SmttStackTailF{}  -> BiFixStk $ SmttStackTailF (fromStackedExpr $ cs `indexEx` 0)
        SmttStackConsF{}  -> BiFixStk $ SmttStackConsF
          (fromValuedExpr $ cs `indexEx` 0)
          (fromStackedExpr $ cs `indexEx` 1)
    where
      fromValuedExpr (ValuedExpr x) = x
      fromValuedExpr _              = error "expected a valued expression"

      fromStackedExpr (StackedExpr x) = x
      fromStackedExpr _               = error "expected a stacked expression"

prettyShowRhs :: (Show s, Show l) => RightHandSide s t l -> String
prettyShowRhs rhs = goStk rhs ""
  where
    goStk (FixStk x) = prettyShowRhsStkF uShow cShow goVal goStk x
    goVal (FixVal x) = prettyShowRhsValF uShow cShow goVal goStk x

    uShow u = S.showString "u" . S.shows u
    cShow c = S.showString "y" . S.shows c

data StackMacroTreeTransducer s ta la tb lb = StackMacroTreeTransducer
  { smttStates      :: HashSet s
  , smttInitialExpr :: RightHandSide s tb lb
  , smttTransRules  :: HashMap (s, la) (RightHandSide s tb lb)
  } deriving (Eq, Generic)

type SmttTransducer s ta tb
  = StackMacroTreeTransducer s ta (LabelType ta) tb (LabelType tb)

type SmttConstraint s ta la tb lb =
  ( RtConstraint ta la
  , RtConstraint tb lb
  , Eq s, Hashable s, RankedLabel s
  , Eq la, Hashable la
  )

instance (Show s, Show la, Show lb, SmttConstraint s ta la tb lb)
    => Show (StackMacroTreeTransducer s ta la tb lb) where

  show StackMacroTreeTransducer{..} = "StackMacroTreeTransducer {"
      <> " smttStates = " <> show (toList smttStates) <> ","
      <> " smttInitialExpr = " <> prettyShowRhs smttInitialExpr <> ","
      <> " smttTransRules = [" <> intercalate ", " (showRule <$> mapToList smttTransRules) <> "],"
      <> " }"
    where
      showRule (k, rhs) = show k <> " -> " <> prettyShowRhs rhs

buildSmtt :: forall m s ta la tb lb. (SmttConstraint s ta la tb lb, MonadThrow m)
  => RightHandSide s tb lb -> [(s, la, RightHandSide s tb lb)]
  -> m (StackMacroTreeTransducer s ta la tb lb)
buildSmtt ie rules = do
    states' <- scanRHSStk 1 0 [] ie
    (states'', rules') <- go rules states' []
    pure StackMacroTreeTransducer
      { smttStates      = setFromList states''
      , smttInitialExpr = ie
      , smttTransRules  = mapFromList rules'
      }
  where
    treeLabelRankIn = treeLabelRank $ Proxy @ta
    treeLabelRankOut = treeLabelRank $ Proxy @tb

    go [] xs ys             = pure (xs, ys)
    go ((s,l,rhs):rs) xs ys = do
      let srank = labelRank s
      when (srank < 1) $ throwErrorM "Not allow states with rank 0"

      states <- scanRHSStk (treeLabelRankIn l) (srank - 1) xs rhs

      let rule = ((s, l), rhs)
      go rs states $ rule:ys

    scanRHSStk p r xs (FixStk rhs) = case rhs of
      SmttContextF i    -> if i < r
        then pure xs
        else throwErrorM "Using an over indexed context parameter"
      SmttStateF s i cs -> if i < p && labelRank s - 1 == length cs
        then foldM (scanRHSStk p r) (s:xs) cs
        else throwErrorM "Using an over indexed subtree"
      SmttStackEmptyF  -> pure xs
      SmttStackTailF s -> scanRHSStk p r xs s
      SmttStackConsF v s -> do
        xs' <- scanRHSVal p r xs v
        scanRHSStk p r xs' s

    scanRHSVal p r xs (FixVal rhs) = case rhs of
      SmttLabelSideF l cs -> if length cs == treeLabelRankOut l
        then foldM (scanRHSVal p r) xs cs
        else throwErrorM "Mismatch the rank of an output label for childs"
      SmttStackBottomF -> pure xs
      SmttStackHeadF s -> scanRHSStk p r xs s
