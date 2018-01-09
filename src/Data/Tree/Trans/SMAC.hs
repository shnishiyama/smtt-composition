{-# LANGUAGE NoStrict        #-}
{-# LANGUAGE OverloadedLists #-}
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

    -- standard form
  , toStandardForm
  , toStackMacroTreeTransducer

    -- reduction system
  , ReductionState
  , buildSmttReduction
  , runSmttReduction
  , runSmttReductionWithHistory
  , toInitialReductionState
  , fromReductionState
  , prettyShowReductionState

    -- internal
  , ReductionStateValF (..)
  , ReductionStateStkF (..)
  , pattern SmttStateF
  , pattern SmttLabelSideF
  , pattern SmttContextF
  , pattern SmttStackBottomF
  , pattern SmttStackHeadF
  , pattern SmttStackEmptyF
  , pattern SmttStackTailF
  , pattern SmttStackConsF
  , smttStates
  , smttInitialExpr
  , smttTransRules
  ) where

import           SattPrelude

import           Data.Bifunctor.FixLR
import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import           Data.Tree.RankedTree.Zipper
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.Stack
import qualified Data.Tree.Trans.MAC as MAC
import qualified Text.Show                   as S


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
  SmttLabelSideF l cs -> S.shows l . S.showString "("
    . foldl' (.) id (intersperse (S.showString ", ") $ vrhsShow <$> cs) . S.showString ")"
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

pattern SmttLabelSide :: RtConstraint t l => l -> NodeVec (RightHandSideVal s t l) -> RightHandSideVal s t l
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
        else throwErrorM
          $  "Using an over indexed context parameter"
          <> " (expected: < " <> show r <> ", actual: " <> show i <> ")"
      SmttStateF s i cs -> if i < p && labelRank s - 1 == length cs
        then foldM (scanRHSStk p r) (s:xs) cs
        else throwErrorM
          $  "Using an over indexed subtree"
          <> " (expected: < " <> show p <> ", actual: " <> show i <> ")"
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

smttTranslateRule :: SmttConstraint s ta la tb lb
  => StackMacroTreeTransducer s ta la tb lb
  -> (s, la) -> RightHandSide s tb lb
smttTranslateRule trans p = fromMaybe SmttStackEmpty
  . lookup p $ smttTransRules trans


-- reduction system

newtype ReductionStateValF s ta la tb lb valstate stkstate = ReductionStateValF
  { unwrapReductionStateValF :: RightHandSideValF s tb lb ta stkstate valstate stkstate
  } deriving (Eq, Ord, Show, Generic)

instance (Eq lb) => Eq2 (ReductionStateValF s ta la tb lb) where
  liftEq2 f g (ReductionStateValF x) (ReductionStateValF y) = case (x, y) of
    (SmttLabelSideF l1 cs1, SmttLabelSideF l2 cs2) -> l1 == l2 && liftEq f cs1 cs2
    (SmttStackBottomF, SmttStackBottomF) -> True
    (SmttStackHeadF s1, SmttStackHeadF s2) -> g s1 s2
    _ -> False

instance (Ord lb) => Ord2 (ReductionStateValF s ta la tb lb) where
  liftCompare2 f g (ReductionStateValF x) (ReductionStateValF y) = case (x, y) of
    (SmttLabelSideF l1 cs1, SmttLabelSideF l2 cs2) -> l1 `compare` l2 <> liftCompare f cs1 cs2
    (SmttLabelSideF{}, _) -> LT
    (_, SmttLabelSideF{}) -> GT
    (SmttStackBottomF, SmttStackBottomF) -> EQ
    (SmttStackBottomF{}, _) -> LT
    (_, SmttStackBottomF{}) -> GT
    (SmttStackHeadF s1, SmttStackHeadF s2) -> g s1 s2

instance (Show lb) => Show2 (ReductionStateValF s ta la tb lb) where
  liftShowsPrec2 f1 f2 g1 _ d (ReductionStateValF x) = S.showParen (d > appPrec) $ case x of
      SmttLabelSideF l cs -> S.showString "SmttLabelSideF "
        . S.showsPrec (appPrec + 1) l
        . S.showString " "
        . liftShowsPrec f1 f2 (appPrec + 1) cs
      SmttStackBottomF -> S.showString "SmttStackBottomF"
      SmttStackHeadF s -> S.showString "SmttStackHeadF "
        . g1 (appPrec + 1) s
    where
      appPrec = 10

instance Bifunctor (ReductionStateValF s ta la tb lb) where
  bimap f g (ReductionStateValF x) = ReductionStateValF $ case x of
    SmttLabelSideF l cs -> SmttLabelSideF l $ f <$> cs
    SmttStackBottomF    -> SmttStackBottomF
    SmttStackHeadF s    -> SmttStackHeadF $ g s

instance Bifoldable (ReductionStateValF s ta la tb lb) where
  bifoldr f g x (ReductionStateValF y) = case y of
    SmttLabelSideF _ cs -> foldr f x cs
    SmttStackBottomF    -> x
    SmttStackHeadF s    -> g s x

  bifoldMap f g (ReductionStateValF y) = case y of
    SmttLabelSideF _ cs -> foldMap f cs
    SmttStackBottomF    -> mempty
    SmttStackHeadF s    -> g s

newtype ReductionStateStkF s ta la tb lb valstate stkstate = ReductionStateStkF
  { unwrapReductionStateStkF :: RightHandSideStkF s tb lb ta stkstate valstate stkstate
  } deriving (Eq, Ord, Show, Generic)

instance (Eq s, Eq ta) => Eq2 (ReductionStateStkF s ta la tb lb) where
  liftEq2 f g (ReductionStateStkF x) (ReductionStateStkF y) = case (x, y) of
    (SmttContextF c1, SmttContextF c2) -> g c1 c2
    (SmttStateF s1 t1 cs1, SmttStateF s2 t2 cs2) ->
      s1 == s2 && t1 == t2 && liftEq g cs1 cs2
    (SmttStackEmptyF, SmttStackEmptyF) -> True
    (SmttStackTailF s1, SmttStackTailF s2) -> g s1 s2
    (SmttStackConsF v1 s1, SmttStackConsF v2 s2) -> f v1 v2 && g s1 s2
    _ -> False

instance (Ord s, Ord ta) => Ord2 (ReductionStateStkF s ta la tb lb) where
  liftCompare2 f g (ReductionStateStkF x) (ReductionStateStkF y) = case (x, y) of
    (SmttContextF c1, SmttContextF c2) -> g c1 c2
    (SmttContextF{}, _) -> LT
    (_, SmttContextF{}) -> GT
    (SmttStateF s1 t1 cs1, SmttStateF s2 t2 cs2) ->
      s1 `compare` s2 <> t1 `compare` t2 <> liftCompare g cs1 cs2
    (SmttStateF{}, _) -> LT
    (_, SmttStateF{}) -> GT
    (SmttStackEmptyF, SmttStackEmptyF) -> EQ
    (SmttStackEmptyF{}, _) -> LT
    (_, SmttStackEmptyF{}) -> GT
    (SmttStackTailF s1, SmttStackTailF s2) -> g s1 s2
    (SmttStackTailF{}, _) -> LT
    (_, SmttStackTailF{}) -> GT
    (SmttStackConsF v1 s1, SmttStackConsF v2 s2) -> f v1 v2 <> g s1 s2

instance (Show s, Show ta) => Show2 (ReductionStateStkF s ta la tb lb) where
  liftShowsPrec2 f1 _ g1 g2 d (ReductionStateStkF x) = S.showParen (d > appPrec) $ case x of
      SmttContextF c -> S.showString "SmttContextF "
        . g1 (appPrec + 1) c
      SmttStateF s t cs -> S.showString "SmttStateF "
        . S.showsPrec (appPrec + 1) s
        . S.showString " "
        . S.showsPrec (appPrec + 1) t
        . S.showString " "
        . liftShowsPrec g1 g2 (appPrec + 1) cs
      SmttStackEmptyF -> S.showString "SmttStackEmptyF"
      SmttStackTailF s -> S.showString "SmttStackTailF "
        . g1 (appPrec + 1) s
      SmttStackConsF v s -> S.showString "SmttStackConsF "
        . f1 (appPrec + 1) v
        . S.showString " "
        . g1 (appPrec + 1) s
    where
      appPrec = 10

instance Bifunctor (ReductionStateStkF s ta la tb lb) where
  bimap f g (ReductionStateStkF x) = ReductionStateStkF $ case x of
    SmttContextF c     -> SmttContextF $ g c
    SmttStateF s t cs  -> SmttStateF s t $ g <$> cs
    SmttStackEmptyF    -> SmttStackEmptyF
    SmttStackTailF s   -> SmttStackTailF $ g s
    SmttStackConsF v s -> SmttStackConsF (f v) (g s)

instance Bifoldable (ReductionStateStkF s ta la tb lb) where
  bifoldr f g x (ReductionStateStkF y) = case y of
    SmttContextF c     -> g c x
    SmttStateF _ _ cs  -> foldr g x cs
    SmttStackEmptyF    -> x
    SmttStackTailF s   -> g s x
    SmttStackConsF v s -> f v $ g s x

  bifoldMap f g (ReductionStateStkF y) = case y of
    SmttContextF c     -> g c
    SmttStateF _ _ cs  -> foldMap g cs
    SmttStackEmptyF    -> mempty
    SmttStackTailF s   -> g s
    SmttStackConsF v s -> f v `mappend` g s

type ReductionState s ta la tb lb = BiStackExprFix
  (ReductionStateValF s ta la tb lb)
  (ReductionStateStkF s ta la tb lb)

type ReductionStateVal s ta la tb lb = FixVal
  (ReductionStateValF s ta la tb lb)
  (ReductionStateStkF s ta la tb lb)

type ReductionStateStk s ta la tb lb = FixStk
  (ReductionStateValF s ta la tb lb)
  (ReductionStateStkF s ta la tb lb)

pattern FixRedVal
  :: RightHandSideValF s tb lb ta
    (ReductionStateStk s ta la tb lb)
    (ReductionStateVal s ta la tb lb)
    (ReductionStateStk s ta la tb lb)
  -> ReductionStateVal s ta la tb lb
pattern FixRedVal v = FixVal (ReductionStateValF v)

{-# COMPLETE FixRedVal #-}

pattern FixRedStk
  :: RightHandSideStkF s tb lb ta
    (ReductionStateStk s ta la tb lb)
    (ReductionStateVal s ta la tb lb)
    (ReductionStateStk s ta la tb lb)
  -> ReductionStateStk s ta la tb lb
pattern FixRedStk s = FixStk (ReductionStateStkF s)

{-# COMPLETE FixRedStk #-}

pattern RedFixVal
  :: RightHandSideValF s tb lb ta
    (ReductionStateStk s ta la tb lb)
    (ReductionStateVal s ta la tb lb)
    (ReductionStateStk s ta la tb lb)
  -> ReductionState s ta la tb lb
pattern RedFixVal v = BiFixVal (ReductionStateValF v)

pattern RedFixStk
  :: RightHandSideStkF s tb lb ta
    (ReductionStateStk s ta la tb lb)
    (ReductionStateVal s ta la tb lb)
    (ReductionStateStk s ta la tb lb)
  -> ReductionState s ta la tb lb
pattern RedFixStk s = BiFixStk (ReductionStateStkF s)

{-# COMPLETE RedFixVal, RedFixStk #-}

instance (SmttConstraint s ta la tb lb) => RankedTree (ReductionState s ta la tb lb) where
  type LabelType (ReductionState s ta la tb lb) = StackExprEither
    (ReductionStateValF s ta la tb lb () ())
    (ReductionStateStkF s ta la tb lb () ())

  treeLabel (BiFixVal x) = ValuedExpr  $ bivoid x
  treeLabel (BiFixStk x) = StackedExpr $ bivoid x

  treeChilds (BiFixVal x) = fromList $ biList $ bimap ValuedExpr StackedExpr x
  treeChilds (BiFixStk x) = fromList $ biList $ bimap ValuedExpr StackedExpr x

  treeLabelRank _ (ValuedExpr  x) = bilength x
  treeLabelRank _ (StackedExpr x) = bilength x

  mkTreeUnchecked e cs = case e of
      ValuedExpr (ReductionStateValF ve) -> RedFixVal $ case ve of
        SmttLabelSideF l _ -> SmttLabelSideF l $ fromValuedExpr <$> cs
        SmttStackBottomF   -> SmttStackBottomF
        SmttStackHeadF{}   -> SmttStackHeadF (fromStackedExpr $ cs `indexEx` 0)
      StackedExpr (ReductionStateStkF se) -> RedFixStk $ case se of
        SmttContextF{} -> SmttContextF (fromStackedExpr $ cs `indexEx` 0)
        SmttStateF s u _ -> SmttStateF s u $ fromStackedExpr <$> cs
        SmttStackEmptyF   -> SmttStackEmptyF
        SmttStackTailF{}  -> SmttStackTailF (fromStackedExpr $ cs `indexEx` 0)
        SmttStackConsF{}  -> SmttStackConsF
          (fromValuedExpr $ cs `indexEx` 0)
          (fromStackedExpr $ cs `indexEx` 1)
    where
      fromValuedExpr (ValuedExpr x) = x
      fromValuedExpr _              = error "expected a valued expression"

      fromStackedExpr (StackedExpr x) = x
      fromStackedExpr _               = error "expected a stacked expression"

buildSmttReduction :: forall tz b s ta la tb lb. (SmttConstraint s ta la tb lb, RankedTreeZipper tz)
  => (RtApply tz (ReductionState s ta la tb lb) -> b -> b) -> b
  -> StackMacroTreeTransducer s ta la tb lb
  -> ReductionState s ta la tb lb
  -> b
buildSmttReduction f is trans = go is . toZipper
  where
    rule = smttTranslateRule trans

    checkReducible (RedFixVal x) = case x of
      SmttLabelSideF{}   -> False
      SmttStackBottomF{} -> False
      SmttStackHeadF{}   -> False
    checkReducible (RedFixStk x) = case x of
      SmttStateF{}      -> True
      SmttStackEmptyF{} -> True
      SmttStackTailF{}  -> False
      SmttStackConsF{}  -> True
      SmttContextF{}    -> error "SmttContext should be reduce in replacements"

    go x sz = case zoomNextRightOutZipper (checkReducible . toTree) sz of
      Just sz' -> let
          !nsz = reductState sz'
          !nx  = f nsz x
        in go nx nsz
      Nothing -> x

    reductState sz = case toTree sz of
      RedFixStk x -> case x of
        SmttStateF s t cs  -> setTreeZipper (reductStateSide s t cs) sz
        SmttStackConsF h t -> deconsStackCons h t sz
        SmttStackEmptyF    -> deconsStackEmpty sz
        _                  -> error "This state is irreducible"
      RedFixVal _ -> error "This state is irreducible"

    reductStateSide s t cs = replaceRHS (treeChilds t) cs
      $ rule (s, treeLabel t)

    deconsStackEmpty sz = case zoomOutRtZipper sz of
      Nothing -> errorUnreachable
      Just nsz -> case toTree nsz of
        RedFixVal x -> case x of
          SmttStackHeadF{} -> setTreeZipper (RedFixVal SmttStackBottomF) nsz
          _                -> errorUnreachable
        RedFixStk x -> case x of
          SmttStackTailF{} -> setTreeZipper (RedFixStk SmttStackEmptyF) nsz
          _                -> errorUnreachable

    deconsStackCons h t sz = case zoomOutRtZipper sz of
      Nothing  -> errorUnreachable
      Just nsz -> case toTree nsz of
        RedFixVal x -> case x of
          SmttStackHeadF{} -> setTreeZipper (ValuedExpr h) nsz
          _                -> errorUnreachable
        RedFixStk x -> case x of
          SmttStackTailF{} -> setTreeZipper (StackedExpr t) nsz
          _                -> errorUnreachable

    replaceRHS us ys = StackedExpr . replaceRHSStk us ys

    replaceRHSVal us ys (FixVal x) = FixRedVal $ case x of
      SmttLabelSideF l cs -> SmttLabelSideF l $ replaceRHSVal us ys <$> cs
      SmttStackBottomF    -> SmttStackBottomF
      SmttStackHeadF s    -> SmttStackHeadF $ replaceRHSStk us ys s

    replaceRHSStk us ys (FixStk x) = case x of
      SmttContextF yi      -> ys `indexEx` yi
      SmttStateF s ui cs   -> FixRedStk $ SmttStateF s (us `indexEx` ui) $ replaceRHSStk us ys <$> cs
      SmttStackEmptyF      -> FixRedStk $ SmttStackEmptyF
      SmttStackTailF s     -> FixRedStk $ SmttStackTailF $ replaceRHSStk us ys s
      SmttStackConsF v s   -> FixRedStk $ SmttStackConsF
        (replaceRHSVal us ys v)
        (replaceRHSStk us ys s)

runSmttReduction :: forall s ta la tb lb.
  ( SmttConstraint s ta la tb lb
  )
  => StackMacroTreeTransducer s ta la tb lb
  -> ReductionState s ta la tb lb
  -> ReductionState s ta la tb lb
runSmttReduction trans istate = toTopTree
  $ buildSmttReduction const (rtZipper istate) trans istate

runSmttReductionWithHistory :: forall s ta la tb lb.
  ( SmttConstraint s ta la tb lb
  )
  => StackMacroTreeTransducer s ta la tb lb
  -> ReductionState s ta la tb lb
  -> [ReductionState s ta la tb lb]
runSmttReductionWithHistory trans istate
  = buildSmttReduction @RTZipper (\tz -> (. (toTopTree tz:))) (istate:) trans istate []

toInitialReductionState :: SmttConstraint s ta la tb lb
  => StackMacroTreeTransducer s ta la tb lb
  -> ta -> ReductionState s ta la tb lb
toInitialReductionState trans t = ValuedExpr . goVal $ FixVal $ SmttStackHeadF $ smttInitialExpr trans
  where
    goVal (FixVal x) = FixRedVal $ case x of
      SmttLabelSideF l cs -> SmttLabelSideF l $ goVal <$> cs
      SmttStackBottomF    -> SmttStackBottomF
      SmttStackHeadF s    -> SmttStackHeadF $ goStk s

    goStk (FixStk x) = FixRedStk $ case x of
      SmttStateF f _ cs  -> SmttStateF f t $ goStk <$> cs
      SmttContextF{}     -> error "This tree transducer is illegal."
      SmttStackEmptyF    -> SmttStackEmptyF
      SmttStackTailF s   -> SmttStackTailF $ goStk s
      SmttStackConsF v s -> SmttStackConsF (goVal v) (goStk s)

fromReductionState :: SmttConstraint s ta la tb lb
  => ReductionState s ta la tb lb -> Maybe tb
fromReductionState x = case x of
    ValuedExpr  x' -> fromReductionStateVal x'
    StackedExpr x' -> fromReductionStateStk x'
  where
    fromReductionStateVal (FixRedVal x') = case x' of
      SmttLabelSideF l cs -> do
        cs' <- mapM fromReductionStateVal cs
        pure $ mkTreeUnchecked l cs'
      SmttStackBottomF    -> pure $ mkTreeUnchecked bottomLabel []
      _ -> Nothing

    fromReductionStateStk (FixRedStk x') = case x' of
      _ -> Nothing

prettyShowReductionState :: (Show s, Show ta, Show lb)
  => ReductionState s ta la tb lb -> String
prettyShowReductionState state = go state ""
  where
    go (ValuedExpr  x) = goVal x
    go (StackedExpr x) = goStk x

    goVal (FixRedVal x) = prettyShowRhsValF S.shows goStk goVal goStk x
    goStk (FixRedStk x) = prettyShowRhsStkF S.shows goStk goVal goStk x


-- A tree transduction for smtts
instance SmttConstraint s ta la tb lb => TreeTransducer (StackMacroTreeTransducer s ta la tb lb) ta tb where
  treeTrans trans
    =   toInitialReductionState trans
    >>> runSmttReduction trans
    >>> fromReductionState
    >>> maybe (throwErrorM "This tree transducer is illegal.") pure


-- standard form

toStandardForm :: SmttConstraint s ta la tb lb
  => StackMacroTreeTransducer s ta la tb lb
  -> StackMacroTreeTransducer s ta la tb lb
toStandardForm trans = trans
    { smttInitialExpr = initialExpr
    , smttTransRules  = rules
    }
  where
    initialExpr = evalStackStkExpr $ smttInitialExpr trans

    rules = evalStackStkExpr <$> smttTransRules trans


toStackMacroTreeTransducer ::
  ( MAC.MttConstraint s ta la tb lb
  )
  => MAC.MacroTreeTransducer s ta la tb lb
  -> StackMacroTreeTransducer s ta la tb lb
toStackMacroTreeTransducer trans = fromMaybe errorUnreachable
    $ buildSmtt
      (convRhs $ MAC.mttInitialExpr trans)
      [ (f, l, convRhs rhs) | ((f, l), rhs) <- mapToList $ MAC.mttTransRules trans ]
  where
    convRhs x = case x of
      MAC.MttContext c       -> SmttContext c
      MAC.MttState f u cs    -> SmttState f u $ convRhs <$> cs
      MAC.MttLabelSide l cs  -> SmttStackCons
        (SmttLabelSide l $ SmttStackHead . convRhs <$> cs)
        SmttStackEmpty
      MAC.MttBottomLabelSide -> SmttStackEmpty
