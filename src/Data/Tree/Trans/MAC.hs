{-# LANGUAGE NoStrict        #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.MAC
  ( -- common
    MacroTreeTransducer
  , MttTransducer
  , MttConstraint
  , buildMtt
  , RightHandSide
  , pattern MttContext
  , pattern MttState
  , pattern MttLabelSide
  , prettyShowRhs

    -- bottom
  , bottomLabelSide

    -- reduction system
  , ReductionState
  , buildMttReduction
  , runMttReduction
  , runMttReductionWithHistory
  , toInitialReductionState
  , fromReductionState
  , prettyShowReductionState

    -- internal
  , mttStates
  , mttInitialExpr
  , mttTransRules
  , RightHandSideF(..)
  , prettyShowRhsF
  , ReductionStateF(..)
  , mttTranslateRule
  ) where

import           SattPrelude

import qualified Data.Foldable               as F
import           Data.Functor.Foldable
import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import           Data.Tree.RankedTree.Zipper
import           Data.Tree.Trans.Class


data RightHandSideF s t l u c rhs
  = MttContextF c
  | MttStateF s u (NodeVec rhs)
  | MttLabelSideF ~l (NodeVec rhs)
  deriving (Eq, Ord, Show, Generic, Generic1, Functor, Foldable)

deriveEq1 ''RightHandSideF
deriveEq2 ''RightHandSideF
deriveOrd1 ''RightHandSideF
deriveOrd2 ''RightHandSideF
deriveShow1 ''RightHandSideF
deriveShow2 ''RightHandSideF
deriveBifunctor ''RightHandSideF
deriveBifoldable ''RightHandSideF

prettyShowRhsF :: (Show s, Show l)
  => (u -> String) -> (c -> String) -> (rhs -> String)
  -> RightHandSideF s t l u c rhs
  -> String
prettyShowRhsF tShow cShow rhsShow x = case x of
  MttContextF c -> cShow c
  MttStateF s t cs -> show s <> "(" <> tShow t
    <> intercalate "" (cs <&> \rhs -> ", " <> rhsShow rhs) <> ")"
  MttLabelSideF l cs -> show l <> "(" <> intercalate ", " (rhsShow <$> cs) <> ")"


type RightHandSide s t l = Fix (RightHandSideF s t l RankNumber RankNumber)

pattern MttContext :: RankNumber -> RightHandSide s t l
pattern MttContext c = Fix (MttContextF c)

pattern MttState :: s -> RankNumber -> NodeVec (RightHandSide s t l) -> RightHandSide s t l
pattern MttState s t cs = Fix (MttStateF s t cs)

pattern MttLabelSide :: l -> NodeVec (RightHandSide s t l) -> RightHandSide s t l
pattern MttLabelSide l cs = Fix (MttLabelSideF l cs)

{-# COMPLETE MttContext, MttState, MttLabelSide #-}

prettyShowRhs :: (Show s, Show l) => RightHandSide s t l -> String
prettyShowRhs (Fix x) = prettyShowRhsF
  (\t -> "u" <> show t)
  (\c -> "y" <> show c)
  prettyShowRhs
  x

bottomLabelSide :: RightHandSide s t l
bottomLabelSide = MttLabelSide bottomLabel []

data MacroTreeTransducer s ta la tb lb = MacroTreeTransducer
  { mttStates      :: HashSet s
  , mttInitialExpr :: RightHandSide s tb lb
  , mttTransRules  :: HashMap (s, la) (RightHandSide s tb lb)
  } deriving (Eq, Generic)

type MttTransducer s ta tb
  = MacroTreeTransducer s ta (LabelType ta) tb (LabelType tb)

type MttConstraint s ta la tb lb =
  ( RtConstraint ta la
  , RtConstraint tb lb
  , Eq s, Hashable s, RankedLabel s
  , Eq la, Hashable la
  )

instance (Show s, Show la, Show lb, MttConstraint s ta la tb lb)
    => Show (MacroTreeTransducer s ta la tb lb) where

  show MacroTreeTransducer{..} = "MacroTreeTransducer {"
      <> " mttStates = " <> show (toList mttStates) <> ","
      <> " mttInitialExpr = " <> prettyShowRhs mttInitialExpr <> ","
      <> " mttTransRules = [" <> intercalate ", " (showRule <$> mapToList mttTransRules) <> "],"
      <> " }"
    where
      showRule (k, rhs) = show k <> " -> " <> prettyShowRhs rhs

buildMtt :: forall m s ta la tb lb. (MttConstraint s ta la tb lb, MonadThrow m)
  => RightHandSide s tb lb -> [(s, la, RightHandSide s tb lb)]
  -> m (MacroTreeTransducer s ta la tb lb)
buildMtt ie rules = do
    states' <- scanRHS 1 0 [] ie
    (states'', rules') <- go rules states' []
    pure MacroTreeTransducer
      { mttStates      = setFromList states''
      , mttInitialExpr = ie
      , mttTransRules  = mapFromList rules'
      }
  where
    treeLabelRankIn = treeLabelRank $ Proxy @ta
    treeLabelRankOut = treeLabelRank $ Proxy @tb

    go [] xs ys             = pure (xs, ys)
    go ((s,l,rhs):rs) xs ys = do
      let srank = labelRank s
      when (srank < 1) $ throwErrorM "Not allow states with rank 0"

      states <- scanRHS (treeLabelRankIn l) (srank - 1) xs rhs

      let rule = ((s, l), rhs)
      go rs states $ rule:ys

    scanRHS p r xs (Fix rhs) = case rhs of
      MttContextF i    -> if i < r
        then pure xs
        else throwErrorM "Using an over indexed context parameter"
      MttStateF s i cs -> if i < p && labelRank s - 1 == length cs
        then foldM (scanRHS p r) (s:xs) cs
        else throwErrorM "Using an over indexed subtree"
      -- ignore labels with rank 0 for bottom
      MttLabelSideF l cs -> let len = length cs in
        if len == 0 || len == treeLabelRankOut l
          then foldM (scanRHS p r) xs cs
          else throwErrorM "Mismatch the rank of an output label for childs"

mttTranslateRule :: MttConstraint s ta la tb lb
  => MacroTreeTransducer s ta la tb lb
  -> (s, la) -> RightHandSide s tb lb
mttTranslateRule trans p = fromMaybe bottomLabelSide . lookup p $ mttTransRules trans


-- reduction system

newtype ReductionStateF s ta la tb lb state = ReductionStateF
  { unwrapReductionStateF :: RightHandSideF s tb lb ta state state
  } deriving (Eq, Ord, Show, Generic)

instance Functor (ReductionStateF s ta la tb lb) where
  fmap f = coerce $ bimap @(RightHandSideF s tb lb ta) f f

instance F.Foldable (ReductionStateF s ta la tb lb) where
  foldMap f = coerce $ bifoldMap @(RightHandSideF s tb lb ta) f f
  foldr f = coerce $ bifoldr @(RightHandSideF s tb lb ta) f f

type instance Element (ReductionStateF s ta la tb lb state) = state

instance MonoFoldable (ReductionStateF s ta la tb lb state)

instance (Eq s, Eq lb, Eq ta) => Eq1 (ReductionStateF s ta la tb lb) where
  liftEq f (ReductionStateF x1) (ReductionStateF x2) = liftEq2 f f x1 x2

instance (Ord s, Ord lb, Ord ta) => Ord1 (ReductionStateF s ta la tb lb) where
  liftCompare f (ReductionStateF x1) (ReductionStateF x2) = liftCompare2 f f x1 x2

instance (Show s, Show lb, Show ta) => Show1 (ReductionStateF s ta la tb lb) where
  liftShowsPrec sPrec sList i (ReductionStateF x) = liftShowsPrec2 sPrec sList sPrec sList i x

type ReductionState s ta la tb lb = Fix (ReductionStateF s ta la tb lb)

pattern RedFix
  :: RightHandSideF s tb lb ta (ReductionState s ta la tb lb) (ReductionState s ta la tb lb)
  -> ReductionState s ta la tb lb
pattern RedFix s = Fix (ReductionStateF s)
{-# COMPLETE RedFix #-}

instance (MttConstraint s ta la tb lb) => RankedTree (Fix (ReductionStateF s ta la tb lb)) where
  type LabelType (Fix (ReductionStateF s ta la tb lb)) = ReductionStateF s ta la tb lb ()

  treeLabel (Fix x) = void x
  treeChilds (RedFix x) = case x of
    MttContextF c      -> [c]
    MttStateF _ _ cs   -> cs
    MttLabelSideF _ cs -> cs

  treeLabelRank _ = length

  mkTreeUnchecked (ReductionStateF x) cs = RedFix $ case x of
    MttContextF _     -> MttContextF $ cs `indexEx` 0
    MttStateF s t _   -> MttStateF s t cs
    MttLabelSideF l _ -> MttLabelSideF l cs

buildMttReduction :: forall tz b s ta la tb lb. (MttConstraint s ta la tb lb, RankedTreeZipper tz)
  => (RtApply tz (ReductionState s ta la tb lb) -> b -> b) -> b
  -> MacroTreeTransducer s ta la tb lb
  -> ReductionState s ta la tb lb
  -> b
buildMttReduction f is trans = go is . toZipper
  where
    rule = mttTranslateRule trans

    checkReducible (RedFix x) = case x of
      MttContextF{}   -> error "MttContext should be reduce in replacements"
      MttStateF{}     -> True
      MttLabelSideF{} -> False

    go x sz = case zoomNextRightOutZipper (checkReducible . toTree) sz of
      Just sz' -> let
        !nsz = modifyTreeZipper reductState sz'
        !nx = f nsz x
        in go nx nsz
      Nothing  -> x

    reductState (RedFix x) = case x of
      MttStateF s t cs -> replaceRHS (treeChilds t) cs $ rule (s, treeLabel t)
      _               -> error "This state is irreducible"

    replaceRHS us ys (Fix x) = case x of
      MttStateF s ui cs  -> RedFix $ MttStateF s (us `indexEx` ui) $ replaceRHS us ys <$> cs
      MttLabelSideF l cs -> RedFix $ MttLabelSideF l $ replaceRHS us ys <$> cs
      MttContextF yi     -> ys `indexEx` yi

runMttReduction :: forall s ta la tb lb. (MttConstraint s ta la tb lb)
  => MacroTreeTransducer s ta la tb lb
  -> ReductionState s ta la tb lb -> ReductionState s ta la tb lb
runMttReduction trans istate = toTopTree $ buildMttReduction const (rtZipper istate) trans istate

runMttReductionWithHistory :: forall s ta la tb lb. (MttConstraint s ta la tb lb)
  => MacroTreeTransducer s ta la tb lb
  -> ReductionState s ta la tb lb -> [ReductionState s ta la tb lb]
runMttReductionWithHistory trans istate
  = buildMttReduction @RTZipper (\tz -> (. (toTopTree tz:))) id trans istate []

toInitialReductionState :: MttConstraint s ta la tb lb
  => MacroTreeTransducer s ta la tb lb -> ta -> ReductionState s ta la tb lb
toInitialReductionState trans t = go $ mttInitialExpr trans
  where
    go (Fix x) = case x of
      MttLabelSideF l cs -> RedFix $ MttLabelSideF l $ go <$> cs
      MttStateF f _ cs   -> RedFix $ MttStateF f t $ go <$> cs
      MttContextF{}      -> error "This tree transducer is illegal."

fromReductionState :: MttConstraint s ta la tb lb
  => ReductionState s ta la tb lb -> Maybe tb
fromReductionState (RedFix (MttLabelSideF l cs)) = do
  cs' <- mapM fromReductionState cs
  pure $ mkTreeUnchecked l cs'
fromReductionState _ = Nothing

prettyShowReductionState :: (Show s, Show ta, Show lb) => ReductionState s ta la tb lb -> String
prettyShowReductionState (RedFix x) = prettyShowRhsF
  show
  prettyShowReductionState
  prettyShowReductionState
  x


-- A tree transduction for mtts
instance MttConstraint s ta la tb lb => TreeTransducer (MacroTreeTransducer s ta la tb lb) ta tb where
  treeTrans trans
    =   toInitialReductionState trans
    >>> runMttReduction trans
    >>> fromReductionState
    >>> maybe (throwErrorM "This tree transducer is illegal.") pure
