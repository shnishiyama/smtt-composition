{-# LANGUAGE NoStrict #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.ATT where

import SattPrelude

import Data.Tree.RankedTree
import Data.Tree.RankedTree.Zipper
import Data.Tree.Trans.Class
import Data.Functor.Foldable
import qualified Unsafe.Coerce as Unsafe


-- strict either
data AttAttrEither syn inh
  = Synthesized syn
  | Inherited inh
  deriving (Eq, Ord, Show, Generic)

deriveEq2 ''AttAttrEither
deriveOrd2 ''AttAttrEither
deriveShow2 ''AttAttrEither
deriveBifunctor ''AttAttrEither
deriveBifoldable ''AttAttrEither

instance (Hashable syn, Hashable inh) => Hashable (AttAttrEither syn inh)


type AttAttrDepend syn inh = AttAttrEither
  (syn, RankNumber)
  inh

data RightHandSideF syn inh l pi rhs
  = AttAttrSideF (AttAttrDepend syn inh) pi
  | AttLabelSideF ~l (NodeVec rhs)
  deriving (Eq, Ord, Show, Generic, Generic1, Functor, Foldable)

deriveEq1 ''RightHandSideF
deriveEq2 ''RightHandSideF
deriveOrd1 ''RightHandSideF
deriveOrd2 ''RightHandSideF
deriveShow1 ''RightHandSideF
deriveShow2 ''RightHandSideF
deriveBifunctor ''RightHandSideF
deriveBifoldable ''RightHandSideF

prettyShowRhsF :: (Show syn, Show inh, Show l)
  => ((AttAttrDepend syn inh, pi) -> String) -> (rhs -> String)
  -> RightHandSideF syn inh l pi rhs
  -> String
prettyShowRhsF attrShow rhsShow x = case x of
  AttAttrSideF a p   -> attrShow (a, p)
  AttLabelSideF l cs -> show l <> "(" <> intercalate ", " (rhsShow <$> cs) <> ")"


type RightHandSide syn inh l = Fix (RightHandSideF syn inh l ())

pattern AttAttrSide :: AttAttrDepend syn inh -> RightHandSide syn inh l
pattern AttAttrSide a = Fix (AttAttrSideF a ())

pattern SynAttrSide :: syn -> RankNumber -> RightHandSide syn inh l
pattern SynAttrSide a i = AttAttrSide (Synthesized (a, i))

pattern InhAttrSide :: inh -> RightHandSide syn inh l
pattern InhAttrSide a = AttAttrSide (Inherited a)

pattern AttLabelSide :: l -> NodeVec (RightHandSide syn inh l) -> RightHandSide syn inh l
pattern AttLabelSide l cs = Fix (AttLabelSideF l cs)

{-# COMPLETE AttAttrSide, AttLabelSide #-}
{-# COMPLETE SynAttrSide, InhAttrSide, AttLabelSide #-}

prettyShowRhs :: (Show syn, Show inh, Show l) => RightHandSide syn inh l -> String
prettyShowRhs (Fix x) = prettyShowRhsF
    (\(a, ()) -> attrShow a)
    prettyShowRhs
    x
  where
    attrShow (Synthesized (a, i)) = show a <> "[" <> show i <> ", ...]"
    attrShow (Inherited a)        = show a <> "[...]"

bottomLabelSide :: RightHandSide syn inh l
bottomLabelSide = AttLabelSide bottomLabel []

type AttAttr syn inh = AttAttrEither
  syn
  (inh, RankNumber)

data AttributedTreeTransducer syn inh ta la tb lb = AttributedTreeTransducer
  { attAttributes   :: HashSet (AttAttrEither syn inh)
  , attInitialAttr  :: syn
  , attInitialRules :: HashMap (AttAttr syn inh) (RightHandSide syn Void lb)
  , attTransRules   :: HashMap (AttAttr syn inh, la) (RightHandSide syn inh lb)
  } deriving (Eq, Generic)

unsafeRhsInhCoerce :: RightHandSide syn Void lb -> RightHandSide syn inh lb
unsafeRhsInhCoerce = Unsafe.unsafeCoerce

unsafeLiftRhsInhCoerce :: Functor f => f (RightHandSide syn Void lb) -> f (RightHandSide syn inh lb)
unsafeLiftRhsInhCoerce = Unsafe.unsafeCoerce

type AttTransducer syn inh ta tb
  = AttributedTreeTransducer syn inh ta (LabelType ta) tb (LabelType tb)

type AttConstraint syn inh ta la tb lb =
  ( RtConstraint ta la
  , RtConstraint tb lb
  , Eq syn, Hashable syn
  , Eq inh, Hashable inh
  , Eq la, Hashable la
  )

instance (Show syn, Show inh, Show la, Show lb, AttConstraint syn inh ta la tb lb)
    => Show (AttributedTreeTransducer syn inh ta la tb lb) where

  show AttributedTreeTransducer{..} = "AttributedTreeTransducer{"
      <> " attAttributes = " <> show (toList attAttributes) <> ","
      <> " attInitialAttr = " <> show attInitialAttr <> ","
      <> " attTranslateRules = ["
        <> intercalate ", " (showInitialRule <$> mapToList attInitialRules)
        <> intercalate ", " (showRule <$> mapToList attTransRules)
      <> "],"
      <> " }"
    where
      showInitialRule (a, rhs) = showRule' "#" a rhs

      showRule ((a, l), rhs) = showRule' (show l) a rhs

      showRule' lshow a rhs
        = attrShow a
        <> " -(" <> lshow <> ")-> "
        <> prettyShowRhs rhs

      attrShow (Synthesized a)    = show a <> "[...]"
      attrShow (Inherited (a, i)) = show a <> "[" <> show i <> ", ...]"

buildAtt :: forall m syn inh ta la tb lb. (AttConstraint syn inh ta la tb lb, MonadThrow m)
  => syn
  -> [(AttAttr syn inh, RightHandSide syn Void lb)]
  -> [(AttAttr syn inh, la, RightHandSide syn inh lb)]
  -> m (AttributedTreeTransducer syn inh ta la tb lb)
buildAtt ia irules rules = do
    attrs' <- foldM (\attrs (a, rhs) -> scanRHS 1 a attrs (unsafeRhsInhCoerce rhs)) [Synthesized ia] irules
    (attrs'', rules') <- go rules attrs' []
    pure AttributedTreeTransducer
      { attAttributes   = setFromList attrs''
      , attInitialAttr  = ia
      , attInitialRules = mapFromList irules
      , attTransRules   = mapFromList rules'
      }
  where
    treeLabelRankIn = treeLabelRank $ Proxy @ta
    treeLabelRankOut = treeLabelRank $ Proxy @tb

    go [] xs ys             = pure (xs, ys)
    go ((a,l,rhs):rs) xs ys = do
      attrs <- scanRHS (treeLabelRankIn l) a xs rhs

      let rule = ((a, l), rhs)
      go rs attrs $ rule:ys

    scanRHS k a xs rhs = do
      xs' <- checkAttr a k xs
      scanRHS' k xs' rhs

    checkAttr (Synthesized a) _ xs = pure $ Synthesized a:xs
    checkAttr (Inherited x) k xs   = case x of
      (a, i) -> if i < k
        then pure $ Inherited a:xs
        else throwErrorM "Using an over indexed inherited attribute"

    scanRHS' k xs (Fix rhs) = case rhs of
      AttAttrSideF (Synthesized x) () -> case x of
        (a, i) -> if i < k
          then pure $ Synthesized a:xs
          else throwErrorM "Using an over indexed synthesized attribute"
      AttAttrSideF (Inherited a) () -> pure $ Inherited a:xs
      -- ignore labels with rank 0 for bottom
      AttLabelSideF l cs -> let len = length cs in
        if len == 0 || len == treeLabelRankOut l
          then foldM (scanRHS' k) xs cs
          else throwErrorM "Mismatch the rank of an output label for childs"

attTranslateRule :: AttConstraint syn inh ta la tb lb
  => AttributedTreeTransducer syn inh ta la tb lb
  -> (AttAttr syn inh) -> Maybe la -> RightHandSide syn inh lb
attTranslateRule trans a ml = fromMaybe bottomLabelSide $ case ml of
  Nothing -> unsafeLiftRhsInhCoerce . lookup a $ attInitialRules trans
  Just l  -> lookup (a, l) $ attTransRules trans


-- reduction system

data AttPathInfo tz = AttPathInfo
  { attPathList   :: [RankNumber]
  , attPathZipper :: tz
  , attIsInitial  :: Bool
  } deriving (Eq, Ord, Show, Generic)

newtype ReductionStateF syn inh ta la tb lb tz state = ReductionStateF
  { unwrapReductionStateF :: RightHandSideF syn inh lb (AttPathInfo tz) state
  } deriving (Eq, Ord, Show, Generic, Functor, Foldable)

type instance Element (ReductionStateF syn inh ta la tb lb tz state) = state

instance MonoFoldable (ReductionStateF syn inh ta la tb lb tz state)

deriveEq1 ''ReductionStateF
deriveOrd1 ''ReductionStateF
deriveShow1 ''ReductionStateF

type ReductionState syn inh ta la tb lb tz = Fix (ReductionStateF syn inh ta la tb lb tz)

pattern RedFix
  :: RightHandSideF syn inh lb (AttPathInfo tz) (ReductionState syn inh ta la tb lb tz)
  -> ReductionState syn inh ta la tb lb tz
pattern RedFix s = Fix (ReductionStateF s)
{-# COMPLETE RedFix #-}

instance (AttConstraint syn inh ta la tb lb) => RankedTree (Fix (ReductionStateF syn inh ta la tb lb tz)) where
  type LabelType (Fix (ReductionStateF syn inh ta la tb lb tz)) = ReductionStateF syn inh ta la tb lb tz ()

  treeLabel (Fix x) = void x
  treeChilds (RedFix x) = case x of
    AttAttrSideF{}     -> []
    AttLabelSideF _ cs -> cs

  treeLabelRank _ = length

  mkTreeUnchecked (ReductionStateF x) cs = RedFix $ case x of
    AttAttrSideF a p -> AttAttrSideF a p
    AttLabelSideF l _ -> AttLabelSideF l cs

buildAttReduction :: forall tz b syn inh ta la tb lb.
  (AttConstraint syn inh ta la tb lb, RankedTreeZipper tz)
  => (RtApply tz (ReductionState syn inh ta la tb lb (tz ta la)) -> b -> b) -> b
  -> AttributedTreeTransducer syn inh ta la tb lb
  -> ReductionState syn inh ta la tb lb (tz ta la)
  -> b
buildAttReduction f is trans = go is . toZipper
  where
    rule = attTranslateRule trans

    checkReducible (RedFix x) = case x of
      AttAttrSideF Inherited{} AttPathInfo{attPathList = []} -> False
      AttAttrSideF{}  -> True
      AttLabelSideF{} -> False

    go x sz = case zoomNextOutRightZipper (checkReducible . toTree) sz of
      Just sz' -> let
        !nsz = modifyTreeZipper reductState sz'
        !nx = f nsz x
        in go nx nsz
      Nothing -> x

    reductState (RedFix x) = case x of
      AttAttrSideF (Synthesized (a, i)) (AttPathInfo pl z True) -> replaceRHS
        (AttPathInfo (i:pl) z False)
        $ rule (Synthesized a) Nothing
      AttAttrSideF (Synthesized (a, i)) (AttPathInfo pl z False) -> replaceRHS
        (AttPathInfo (i:pl) (fromMaybe (error "Using over indexed synthesized attribute") $ zoomInIdxRtZipper i z) False)
        $ rule (Synthesized a) (Just $ toTreeLabel z)
      AttAttrSideF (Inherited a) (AttPathInfo (i:pl) z False) -> case zoomOutRtZipper z of
        Just z' -> replaceRHS (AttPathInfo pl z' False) $ rule (Inherited (a, i)) (Just $ toTreeLabel z')
        Nothing -> replaceRHS (AttPathInfo pl z True) $ rule (Inherited (a, i)) Nothing
      _ -> error "This state is irreducible"

    replaceRHS p (Fix x) = case x of
      AttAttrSideF a _ -> RedFix $ AttAttrSideF a p
      AttLabelSideF l cs -> RedFix $ AttLabelSideF l $ replaceRHS p <$> cs

runAttReduction :: forall syn inh ta la tb lb tz. (AttConstraint syn inh ta la tb lb, RankedTreeZipper tz)
  => AttributedTreeTransducer syn inh ta la tb lb
  -> ReductionState syn inh ta la tb lb (tz ta la) -> ReductionState syn inh ta la tb lb (tz ta la)
runAttReduction trans istate = toTopTree $ buildAttReduction const (toZipper istate) trans istate

runAttReductionWithHistory :: forall syn inh ta la tb lb tz. (AttConstraint syn inh ta la tb lb, RankedTreeZipper tz)
  => AttributedTreeTransducer syn inh ta la tb lb
  -> ReductionState syn inh ta la tb lb (tz ta la) -> [ReductionState syn inh ta la tb lb (tz ta la)]
runAttReductionWithHistory trans istate
  = buildAttReduction (\tz -> (. (toTopTree tz:))) id trans istate []

toInitialReductionState :: forall tz syn inh ta la tb lb.(AttConstraint syn inh ta la tb lb, RankedTreeZipper tz)
  => AttributedTreeTransducer syn inh ta la tb lb -> Bool -> ta -> ReductionState syn inh ta la tb lb (tz ta la)
toInitialReductionState trans b t = replaceRHS (AttPathInfo [] (toZipper t) b) $ attTranslateRule trans (Synthesized $ attInitialAttr trans) Nothing
  where
    replaceRHS p (Fix x) = case x of
      AttAttrSideF a _ -> RedFix $ AttAttrSideF a p
      AttLabelSideF l cs -> RedFix $ AttLabelSideF l $ replaceRHS p <$> cs

fromReductionState :: (AttConstraint syn inh ta la tb lb, RankedTreeZipper tz)
  => ReductionState syn inh ta la tb lb (tz ta la) -> Maybe tb
fromReductionState (RedFix (AttLabelSideF l cs)) = do
  cs' <- mapM fromReductionState cs
  pure $ mkTreeUnchecked l cs'
fromReductionState _ = Nothing

prettyShowReductionState :: (Show syn, Show inh, Show la, Show lb, RtConstraint ta la, RankedTreeZipper tz)
  => ReductionState syn inh ta la tb lb (tz ta la) -> String
prettyShowReductionState (RedFix x) = prettyShowRhsF
    (\(a, AttPathInfo pl z b) -> attrShow a pl z b)
    prettyShowReductionState
    x
  where
    attrShow a pl z b = case a of
      Synthesized (a', i) -> show a' <> show (i:pl) <> "(" <> labelShow z b <> ")"
      Inherited   a'      -> show a' <> show pl <> "(" <> labelShow z b <> ")"

    labelShow _ True  = "#"
    labelShow z False = show $ toTreeLabel z


-- A tree transduction for att
instance AttConstraint syn inh ta la tb lb => TreeTransducer (AttributedTreeTransducer syn inh ta la tb lb) ta tb where
  treeTrans trans
    =   (toInitialReductionState @RTZipper trans True)
    >>> runAttReduction trans
    >>> fromReductionState
    >>> maybe (throwErrorM "This tree transducer is illegal.") pure
