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
  , pattern MttBottomLabelSide
  , prettyShowRhs

    -- reduction system
  , ReductionState
  , buildMttReduction
  , runMttReduction
  , runMttReductionWithHistory
  , toInitialReductionState
  , fromReductionState
  , prettyShowReductionState

    -- internal
  , pattern RedFix
  , mttStates
  , mttInitialExpr
  , mttTransRules
  , RightHandSideF(..)
  , prettyShowRhsF
  , ReductionStateF(..)
  , mttTranslateRule
  ) where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import           Data.Tree.RankedTree.Zipper
import           Data.Tree.Trans.Class
import qualified Text.PrettyPrint.Classy     as Pretty
import qualified Text.Show                   as S


data RightHandSideF s t l u c rhs
  = MttContextF c
  | MttStateF s u (NodeVec rhs)
  | MttLabelSideF l (NodeVec rhs)
  | MttBottomLabelSideF
  deriving (Eq, Ord, Show, Generic, Generic1, Functor, Foldable, Hashable, Hashable1)

deriveEq1 ''RightHandSideF
deriveEq2 ''RightHandSideF
deriveOrd1 ''RightHandSideF
deriveOrd2 ''RightHandSideF
deriveShow1 ''RightHandSideF
deriveShow2 ''RightHandSideF
deriveBifunctor ''RightHandSideF
deriveBifoldable ''RightHandSideF

type instance Element (RightHandSideF s t l u c rhs) = rhs

instance MonoFoldable (RightHandSideF s t l u c rhs)

prettyShowRhsF :: (Show s, Show l)
  => (u -> S.ShowS) -> (c -> S.ShowS) -> (rhs -> S.ShowS)
  -> RightHandSideF s t l u c rhs
  -> S.ShowS
prettyShowRhsF tShow cShow rhsShow x = case x of
    MttContextF c -> cShow c
    MttStateF s t cs -> S.shows s . S.showString "(" . tShow t
      . joinShows (cs <&> \rhs -> S.showString ", " . rhsShow rhs) . S.showString ")"
    MttLabelSideF l cs -> S.shows l . S.showString "("
      . joinShows (intersperse (S.showString ", ") $ rhsShow <$> cs) . S.showString ")"
    MttBottomLabelSideF -> S.showString "_|_"
  where
    joinShows = foldl' (.) id


type RightHandSide s t l = Fix (RightHandSideF s t l RankNumber RankNumber)

pattern MttContext :: RankNumber -> RightHandSide s t l
pattern MttContext c = Fix (MttContextF c)

pattern MttState :: s -> RankNumber -> NodeVec (RightHandSide s t l) -> RightHandSide s t l
pattern MttState s t cs = Fix (MttStateF s t cs)

pattern MttLabelSide :: l -> NodeVec (RightHandSide s t l) -> RightHandSide s t l
pattern MttLabelSide l cs = Fix (MttLabelSideF l cs)

pattern MttBottomLabelSide :: RightHandSide s t l
pattern MttBottomLabelSide = Fix MttBottomLabelSideF

{-# COMPLETE MttContext, MttState, MttLabelSide, MttBottomLabelSide #-}

instance (RtConstraint t l) => RankedTree (RightHandSide s t l) where
  type LabelType (RightHandSide s t l) = RightHandSideF s t l RankNumber RankNumber ()

  treeLabel (Fix x) = void x
  treeChilds (Fix x) = fromList $ toList x

  treeLabelRank _ = length

  mkTreeUnchecked x cs = Fix $ case x of
    MttStateF s u _     -> MttStateF s u cs
    MttContextF c       -> MttContextF c
    MttLabelSideF l _   -> MttLabelSideF l cs
    MttBottomLabelSideF -> MttBottomLabelSideF

prettyShowRhs :: (Show s, Show l) => RightHandSide s t l -> String
prettyShowRhs rhs = go rhs ""
  where
    go (Fix x) = prettyShowRhsF
      (\t -> S.showString "u" . S.shows t)
      (\c -> S.showString "y" . S.shows c)
      go x

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

instance (Show s, Show la, Show lb, MttConstraint s ta la tb lb)
    => Pretty.Pretty (MacroTreeTransducer s ta la tb lb) where

  pretty MacroTreeTransducer{..} = Pretty.record "MacroTreeTransducer"
      [ ("mttStates",      Pretty.list $ Pretty.prettyShowString <$> toList mttStates)
      , ("mttInitialExpr", Pretty.text $ prettyShowRhs mttInitialExpr)
      , ( "mttTransRules"
        , Pretty.list [ showRule f l rhs | (f, l, rhs) <- rules ]
        )
      ]
    where
      rules = sortWith (\(f, l, _) -> (l, f))
        [ (show f, show l, rhs) | ((f, l), rhs) <- mapToList mttTransRules ]

      showRule f l rhs
        = Pretty.text f Pretty.<+> Pretty.text ("(" <> l <> ")")
        Pretty.<+> Pretty.text "->"
        Pretty.<+> Pretty.string (prettyShowRhs rhs)


buildMtt :: forall m s ta la tb lb. (MttConstraint s ta la tb lb, MonadThrow m)
  => RightHandSide s tb lb -> [(s, la, RightHandSide s tb lb)]
  -> m (MacroTreeTransducer s ta la tb lb)
buildMtt ie rules = do
    states' <- scanRHS 1 0 [] ie
    (states'', rules') <- go rules states' []
    let statesSet = setFromList states''
    pure MacroTreeTransducer
      { mttStates      = statesSet
      , mttInitialExpr = ie
      , mttTransRules  = mapFromList
        $ filter (\((f, _), _) -> member f statesSet) rules'
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
      MttLabelSideF l cs -> if length cs == treeLabelRankOut l
        then foldM (scanRHS p r) xs cs
        else throwErrorM "Mismatch the rank of an output label for childs"
      MttBottomLabelSideF -> pure xs

mttTranslateRule :: MttConstraint s ta la tb lb
  => MacroTreeTransducer s ta la tb lb
  -> (s, la) -> RightHandSide s tb lb
mttTranslateRule trans p = fromMaybe MttBottomLabelSide
  . lookup p $ mttTransRules trans


-- reduction system

newtype ReductionStateF c s ta la tb lb state = ReductionStateF
  { unwrapReductionStateF :: RightHandSideF s tb lb ta c state
  } deriving (Eq, Ord, Show, Generic, Functor, Foldable)

deriveEq1 ''ReductionStateF
deriveOrd1 ''ReductionStateF
deriveShow1 ''ReductionStateF

type instance Element (ReductionStateF c s ta la tb lb state) = state

instance MonoFoldable (ReductionStateF c s ta la tb lb state)

type ReductionState c s ta la tb lb = Fix (ReductionStateF c s ta la tb lb)

pattern RedFix
  :: RightHandSideF s tb lb ta c (ReductionState c s ta la tb lb)
  -> ReductionState c s ta la tb lb
pattern RedFix s = Fix (ReductionStateF s)
{-# COMPLETE RedFix #-}

instance (MttConstraint s ta la tb lb) => RankedTree (ReductionState c s ta la tb lb) where
  type LabelType (ReductionState c s ta la tb lb) = ReductionStateF c s ta la tb lb ()

  treeLabel (Fix x) = void x
  treeChilds (Fix x) = fromList $ toList x

  treeLabelRank _ = length

  mkTreeUnchecked (ReductionStateF x) cs = RedFix $ case x of
    MttContextF y       -> MttContextF y
    MttStateF s t _     -> MttStateF s t cs
    MttLabelSideF l _   -> MttLabelSideF l cs
    MttBottomLabelSideF -> MttBottomLabelSideF

buildMttReduction :: forall tz b c s ta la tb lb. (MttConstraint s ta la tb lb, RankedTreeZipper tz)
  => (RtApply tz (ReductionState c s ta la tb lb) -> b -> b) -> b
  -> MacroTreeTransducer s ta la tb lb
  -> ReductionState c s ta la tb lb
  -> b
buildMttReduction f is trans = go is . toZipper
  where
    rule = mttTranslateRule trans

    checkReducible (RedFix x) = case x of
      MttStateF{}           -> True
      MttLabelSideF{}       -> False
      MttBottomLabelSideF{} -> False
      MttContextF{}         -> False

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
      MttContextF yi      -> ys `indexEx` yi
      MttStateF s ui cs   -> RedFix $ MttStateF s (us `indexEx` ui) $ replaceRHS us ys <$> cs
      MttLabelSideF l cs  -> RedFix $ MttLabelSideF l $ replaceRHS us ys <$> cs
      MttBottomLabelSideF -> RedFix MttBottomLabelSideF

runMttReduction :: forall c s ta la tb lb. (MttConstraint s ta la tb lb)
  => MacroTreeTransducer s ta la tb lb
  -> ReductionState c s ta la tb lb -> ReductionState c s ta la tb lb
runMttReduction trans istate = toTopTree
  $ buildMttReduction const (rtZipper istate) trans istate

runMttReductionWithHistory :: forall c s ta la tb lb. (MttConstraint s ta la tb lb)
  => MacroTreeTransducer s ta la tb lb
  -> ReductionState c s ta la tb lb -> [ReductionState c s ta la tb lb]
runMttReductionWithHistory trans istate
  = buildMttReduction @RTZipper (\tz -> (. (toTopTree tz:))) (istate:) trans istate []

toInitialReductionState :: MttConstraint s ta la tb lb
  => MacroTreeTransducer s ta la tb lb
  -> ta -> ReductionState c s ta la tb lb
toInitialReductionState trans t = go $ mttInitialExpr trans
  where
    go (Fix x) = RedFix $ case x of
      MttLabelSideF l cs  -> MttLabelSideF l $ go <$> cs
      MttBottomLabelSideF -> MttBottomLabelSideF
      MttStateF f _ cs    -> MttStateF f t $ go <$> cs
      MttContextF{}       -> error "This tree transducer is illegal."

fromReductionState :: MttConstraint s ta la tb lb
  => ReductionState c s ta la tb lb -> Maybe tb
fromReductionState (RedFix x) = case x of
  MttLabelSideF l cs -> do
    cs' <- traverse fromReductionState cs
    pure $ mkTreeUnchecked l cs'
  MttBottomLabelSideF -> pure $ mkTreeUnchecked bottomLabel []
  _ -> Nothing

prettyShowReductionState :: (Show c, Show s, Show ta, Show lb) => ReductionState c s ta la tb lb -> String
prettyShowReductionState redState = go redState ""
  where
    go (RedFix x) = prettyShowRhsF S.shows S.shows go x


-- A tree transduction for mtts
instance MttConstraint s ta la tb lb => TreeTransducer (MacroTreeTransducer s ta la tb lb) ta tb where
  treeTrans trans
    =   toInitialReductionState trans
    >>> runMttReduction trans
    >>> fromReductionState
    >>> maybe (throwErrorM "This tree transducer is illegal.") pure
