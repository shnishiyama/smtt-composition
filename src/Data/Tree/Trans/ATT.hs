{-# LANGUAGE NoStrict        #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.ATT
  ( -- common
    AttributedTreeTransducer
  , AttTransducer
  , AttConstraint
  , buildAtt
  , AttAttrDepend
  , AttAttr
  , RightHandSide
  , pattern AttAttrSide
  , pattern SynAttrSide
  , pattern InhAttrSide
  , pattern AttLabelSide
  , pattern AttBottomLabelSide
  , prettyShowRhs

    -- either utility
  , AttAttrEither(..)
  , isSynthesized
  , isInherited

    -- reduction system
  , ReductionState
  , ReductionStateWithEmptySyn
  , buildAttReduction
  , runAttReduction
  , runAttReductionWithHistory
  , toInitialReductionState
  , toInitialAttrState
  , fromReductionState
  , prettyShowReductionState

    -- internal
  , attAttributes
  , attInitialAttr
  , attInitialRules
  , attTransRules
  , RightHandSideF(..)
  , prettyShowRhsF
  , ReductionStateF(..)
  , attInitialRule
  , attTranslateRule
  , AttPathInfo(..)
  , pattern AttPathInfo
  , attPathList
  , attNonPathZipper
  , attIsInitial
  , _attPathList
  , emptyAttPathInfo
  , emptyAttPathInfoFromZipper
  , zoomInIdxPathInfo
  , pattern RedFix
  ) where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Zipper
import           Data.Tree.Trans.Class
import qualified Text.Show                   as S


-- TODO: Use Either (GHC 8.2.x have a critical bug for pattern synonyms)
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

isSynthesized :: AttAttrEither syn inh -> Bool
isSynthesized Synthesized{} = True
isSynthesized _             = False

isInherited :: AttAttrEither syn inh -> Bool
isInherited Inherited{} = True
isInherited _           = False


type AttAttrDepend syn inh = AttAttrEither
  (syn, RankNumber)
  inh

data RightHandSideF syn inh t l pi rhs
  = AttAttrSideF (AttAttrDepend syn inh) pi
  | AttLabelSideF l (NodeVec rhs)
  | AttBottomLabelSideF
  deriving (Eq, Ord, Show, Generic, Generic1, Functor, Foldable)

instance (Hashable syn, Hashable inh, Hashable l, Hashable pi, Hashable rhs)
  => Hashable (RightHandSideF syn inh t l pi rhs)

type instance Element (RightHandSideF syn inh t l pi rhs) = rhs

instance MonoFoldable (RightHandSideF syn inh t l pi rhs)

deriveEq1 ''RightHandSideF
deriveEq2 ''RightHandSideF
deriveOrd1 ''RightHandSideF
deriveOrd2 ''RightHandSideF
deriveShow1 ''RightHandSideF
deriveShow2 ''RightHandSideF
deriveBifunctor ''RightHandSideF
deriveBifoldable ''RightHandSideF

prettyShowRhsF :: (Show l, RtConstraint t l)
  => ((AttAttrDepend syn inh, pi) -> S.ShowS)
  -> (rhs -> S.ShowS)
  -> RightHandSideF syn inh t l pi rhs
  -> S.ShowS
prettyShowRhsF attrShow rhsShow x = case x of
  AttAttrSideF a p    -> attrShow (a, p)
  AttLabelSideF l cs  -> S.shows l . S.showString "(" . foldl' (.) id (intersperse (S.showString ", ") $ rhsShow <$> cs) . S.showString ")"
  AttBottomLabelSideF -> S.showString "_|_"


type RightHandSide syn inh t l = Fix (RightHandSideF syn inh t l ())

pattern AttAttrSide :: RtConstraint t l => AttAttrDepend syn inh -> RightHandSide syn inh t l
pattern AttAttrSide a = Fix (AttAttrSideF a ())

pattern SynAttrSide :: RtConstraint t l => syn -> RankNumber -> RightHandSide syn inh t l
pattern SynAttrSide a i = AttAttrSide (Synthesized (a, i))

pattern InhAttrSide :: RtConstraint t l => inh -> RightHandSide syn inh t l
pattern InhAttrSide a = AttAttrSide (Inherited a)

pattern AttLabelSide :: RtConstraint t l => l -> NodeVec (RightHandSide syn inh t l) -> RightHandSide syn inh t l
pattern AttLabelSide l cs = Fix (AttLabelSideF l cs)

pattern AttBottomLabelSide :: RtConstraint t l => RightHandSide syn inh t l
pattern AttBottomLabelSide = Fix AttBottomLabelSideF

{-# COMPLETE AttAttrSide, AttLabelSide, AttBottomLabelSide #-}
{-# COMPLETE SynAttrSide, InhAttrSide, AttLabelSide, AttBottomLabelSide #-}

instance (RtConstraint t l) => RankedTree (RightHandSide syn inh t l) where
  type LabelType (RightHandSide syn inh t l) = RightHandSideF syn inh t l () ()

  treeLabel (Fix x) = void x
  treeChilds (Fix x) = fromList $ toList x

  treeLabelRank _ = length

  mkTreeUnchecked x cs = Fix $ case x of
    AttAttrSideF a p    -> AttAttrSideF a p
    AttLabelSideF l _   -> AttLabelSideF l cs
    AttBottomLabelSideF -> AttBottomLabelSideF

prettyShowRhs :: (Show syn, Show inh, Show l, RtConstraint t l)
  => RightHandSide syn inh t l -> String
prettyShowRhs rhs = go rhs ""
  where
    go (Fix x) = prettyShowRhsF (\(a, ()) -> attrShow a) go x

    attrShow (Synthesized (a, i)) = S.shows a . S.showString "[" . S.shows i . S.showString ", ...]"
    attrShow (Inherited a)        = S.shows a . S.showString "[...]"

type AttAttr syn inh = AttAttrEither
  syn
  (inh, RankNumber)

data AttributedTreeTransducer syn inh ta la tb lb = AttributedTreeTransducer
  { attAttributes   :: HashSet (AttAttrEither syn inh)
  , attInitialAttr  :: syn
  , attInitialRules :: HashMap (AttAttrEither () inh) (RightHandSide syn inh tb lb)
  , attTransRules   :: HashMap (AttAttr syn inh, la) (RightHandSide syn inh tb lb)
  } deriving (Eq, Generic)

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
      <> " attTranslateRules = [" <> intercalate ", "
        (  (showInitialRule <$> mapToList attInitialRules)
        <> (showRule <$> mapToList attTransRules)
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

coerceRhsInh :: forall syn inh tb lb. RightHandSide syn Void tb lb -> RightHandSide syn inh tb lb
coerceRhsInh (Fix x) = Fix $ case x of
  AttAttrSideF a ()   -> AttAttrSideF (second absurd a) ()
  AttLabelSideF l cs  -> AttLabelSideF l $ coerceRhsInh <$> cs
  AttBottomLabelSideF -> AttBottomLabelSideF

buildAtt :: forall m syn inh ta la tb lb. (AttConstraint syn inh ta la tb lb, MonadThrow m)
  => syn
  -> [(AttAttrEither () inh, RightHandSide syn Void tb lb)]
  -> [(AttAttr syn inh, la, RightHandSide syn inh tb lb)]
  -> m (AttributedTreeTransducer syn inh ta la tb lb)
buildAtt ia irules rules = do
    let attrs0 = [Synthesized ia]
    (attrs1, irules') <- goInitial irules attrs0 []
    (attrs2, rules') <- go rules attrs1 []
    pure AttributedTreeTransducer
      { attAttributes   = setFromList attrs2
      , attInitialAttr  = ia
      , attInitialRules = mapFromList irules'
      , attTransRules   = mapFromList rules'
      }
  where
    treeLabelRankIn = treeLabelRank $ Proxy @ta
    treeLabelRankOut = treeLabelRank $ Proxy @tb

    goInitial []            xs ys = pure (xs, ys)
    goInitial ((a, rhs):rs) xs ys = do
      let rhs' = coerceRhsInh rhs
      let attrs = first (const ia) a:xs

      attrs' <- scanRHS 1 attrs rhs'

      let irule = (a, rhs')
      goInitial rs attrs' $ irule:ys

    go [] xs ys             = pure (xs, ys)
    go ((a,l,rhs):rs) xs ys = do
      let k = treeLabelRankIn l
      attrs' <- checkAttr a k xs

      attrs'' <- scanRHS k attrs' rhs

      let rule = ((a, l), rhs)
      go rs attrs'' $ rule:ys

    checkAttr (Synthesized a)    _ xs = pure $ Synthesized a:xs
    checkAttr (Inherited (a, i)) k xs
      | i < k     = pure $ Inherited a:xs
      | otherwise = throwErrorM "Using an over indexed inherited attribute"

    scanRHS k xs (Fix rhs) = case rhs of
      AttAttrSideF (Synthesized (a, i)) () -> if i < k
        then pure $ Synthesized a:xs
        else throwErrorM "Using an over indexed synthesized attribute"
      AttAttrSideF (Inherited a) () -> pure $ Inherited a:xs
      AttLabelSideF l cs -> if length cs == treeLabelRankOut l
        then foldM (scanRHS k) xs cs
        else throwErrorM "Mismatch the rank of an output label for childs"
      AttBottomLabelSideF -> pure xs

attInitialRule :: AttConstraint syn inh ta la tb lb
  => AttributedTreeTransducer syn inh ta la tb lb
  -> AttAttrEither syn inh -> RightHandSide syn inh tb lb
attInitialRule trans a = fromMaybe AttBottomLabelSide $ case a of
    Inherited   a' -> go $ Inherited a'
    Synthesized a' -> if a' == attInitialAttr trans then go $ Synthesized () else Nothing
  where
    go attr = lookup attr $ attInitialRules trans

attTranslateRule :: AttConstraint syn inh ta la tb lb
  => AttributedTreeTransducer syn inh ta la tb lb
  -> AttAttr syn inh -> la -> RightHandSide syn inh tb lb
attTranslateRule trans a l = fromMaybe AttBottomLabelSide $ lookup (a, l) $ attTransRules trans


-- reduction system

data AttPathInfo tz t l = InternalAttPathInfo
  { internalAttRtPathZipper :: RtPathZipper tz t l
  , internalAttIsInitial    :: Bool
  } deriving (Eq, Ord, Show, Generic)

pattern AttPathInfo :: [RankNumber] -> tz t l -> Bool -> AttPathInfo tz t l
pattern AttPathInfo{attPathList,attNonPathZipper,attIsInitial} = InternalAttPathInfo
  { internalAttRtPathZipper = RtPathZipper
    { rtPathList            = attPathList
    , rtPathInternalZipper  = attNonPathZipper
    }
  , internalAttIsInitial    = attIsInitial
  }

{-# COMPLETE AttPathInfo #-}

attRtPathZipper :: Lens' (AttPathInfo tz t l) (RtPathZipper tz t l)
attRtPathZipper = lens internalAttRtPathZipper $ \p rtz ->
  p { internalAttRtPathZipper = rtz }

_attPathList :: Lens' (AttPathInfo tz t l) [RankNumber]
_attPathList = lens attPathList $ \p pl ->
  p { attPathList = pl }

emptyAttPathInfo :: forall tz t l. (RtConstraint t l, RankedTreeZipper tz)
  => Bool -> t -> AttPathInfo tz t l
emptyAttPathInfo b = emptyAttPathInfoFromZipper b . toZipper

emptyAttPathInfoFromZipper :: forall tz t l. (RtConstraint t l, RankedTreeZipper tz)
  => Bool -> tz t l -> AttPathInfo tz t l
emptyAttPathInfoFromZipper b tz = AttPathInfo
  { attPathList      = []
  , attNonPathZipper = tz
  , attIsInitial     = b
  }

zoomInIdxPathInfo :: (RankedTreeZipper tz, RtConstraint t l)
  => RankNumber -> AttPathInfo tz t l -> Maybe (AttPathInfo tz t l)
zoomInIdxPathInfo i p@AttPathInfo{ attIsInitial = True }
  | i == 0    = Just $ p
    { attPathList  = i:attPathList p
    , attIsInitial = False
    }
  | otherwise = Nothing
zoomInIdxPathInfo i p@AttPathInfo{ attIsInitial = False }
  = zoomInIdxRtZipper i p

-- | A zipper for att traversaling
--
-- Examples:
--
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.RankedTree.Label
-- >>> type ABCAlphabet = TaggedRankedAlphabet ['("A", 2), '("B", 1), '("C", 0)]
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> :{
-- treeABCSample :: RankedLabelledTree ABCAlphabet
-- treeABCSample = mkLabelledTree a
--   [ mkTree c []
--   , mkTree b [mkTree c []]
--   ]
-- :}
--
-- >>> treeABCZipper = toZipper @(AttPathInfo RTZipper) treeABCSample
-- >>> toTree <$> zoomInRtZipper treeABCZipper
-- Just C
-- >>> toTree <$> (zoomInRtZipper >=> zoomRightRtZipper) treeABCZipper
-- Just B(C)
-- >>> :{
--   toTree <$>
--   (   zoomInRtZipper
--   >=> zoomRightRtZipper
--   >=> zoomOutRtZipper
--   ) treeABCZipper
-- :}
-- Just A(C,B(C))
--
-- >>> :{
-- toTopTree
--   <$> setTreeZipper (mkTree a [mkTree c [], mkTree c []])
--   <$> zoomInRtZipper treeABCZipper
-- :}
-- Just A(A(C,C),B(C))
--
-- >>> toTree <$> zoomOutRtZipper treeABCZipper
-- Nothing
-- >>> toTree <$> zoomRightRtZipper treeABCZipper
-- Nothing
-- >>> toTree <$> (zoomNextRightOutZipper (const True) <=< zoomInRtZipper) treeABCZipper
-- Just C
-- >>> toTree <$> (zoomNextRightOutZipper1 (const True) <=< zoomInRtZipper) treeABCZipper
-- Just B(C)
--
instance RankedTreeZipper tz => RankedTreeZipper (AttPathInfo tz) where
  toZipper = emptyAttPathInfo False
  toTree p = p ^. attRtPathZipper . to toTree

  zoomInIdxRtZipper n = traverseOf attRtPathZipper $ zoomInIdxRtZipper n
  zoomOutRtZipper = traverseOf attRtPathZipper zoomOutRtZipper
  zoomLeftRtZipper = traverseOf attRtPathZipper zoomLeftRtZipper
  zoomRightRtZipper = traverseOf attRtPathZipper zoomRightRtZipper
  modifyTreeZipper f = attRtPathZipper %~ modifyTreeZipper f
  setTreeZipper t = attRtPathZipper %~ setTreeZipper t

newtype ReductionStateF syn inh ta la tb lb tz state = ReductionStateF
  { unwrapReductionStateF :: RightHandSideF syn inh tb lb (AttPathInfo tz ta la) state
  } deriving (Eq, Ord, Show, Eq1, Ord1, Show1, Generic, Generic1, Functor, Foldable)

type instance Element (ReductionStateF syn inh ta la tb lb tz state) = state

instance MonoFoldable (ReductionStateF syn inh ta la tb lb tz state)

type ReductionState syn inh ta la tb lb tz = Fix (ReductionStateF syn inh ta la tb lb tz)

pattern RedFix
  :: RightHandSideF syn inh tb lb (AttPathInfo tz ta la) (ReductionState syn inh ta la tb lb tz)
  -> ReductionState syn inh ta la tb lb tz
pattern RedFix s = Fix (ReductionStateF s)
{-# COMPLETE RedFix #-}

instance (AttConstraint syn inh ta la tb lb) => RankedTree (ReductionState syn inh ta la tb lb tz) where
  type LabelType (ReductionState syn inh ta la tb lb tz) = ReductionStateF syn inh ta la tb lb tz ()

  treeLabel (Fix x) = void x
  treeChilds (RedFix x) = fromList $ toList x

  treeLabelRank _ = length

  mkTreeUnchecked (ReductionStateF x) cs = RedFix $ case x of
    AttAttrSideF a p    -> AttAttrSideF a p
    AttLabelSideF l _   -> AttLabelSideF l cs
    AttBottomLabelSideF -> AttBottomLabelSideF

type ReductionStateWithEmptySyn syn inh ta la tb lb tz
  = Either (Bool, tz ta la, syn) (ReductionState syn inh ta la tb lb tz)

buildAttReduction :: forall tz b syn inh ta la tb lb.
  (AttConstraint syn inh ta la tb lb, RankedTreeZipper tz)
  => (RtApply tz (ReductionState syn inh ta la tb lb tz) -> b -> b) -> b
  -> AttributedTreeTransducer syn inh ta la tb lb
  -> ReductionStateWithEmptySyn syn inh ta la tb lb tz
  -> b
buildAttReduction f is trans mt = go is' initialZipper
  where
    (initialZipper, is') = case mt of
      Left (b, tz, a) -> let
          !sz   = toZipper $ toRedState b tz a
          !nis = f sz is
        in (sz, nis)
      Right s         -> (toZipper s, is)

    initialRule = attInitialRule trans
    rule = attTranslateRule trans

    toRedState True  tz a = toRedState' True  tz $ initialRule (Synthesized a)
    toRedState False tz a = toRedState' False tz $ rule (Synthesized a) (toTreeLabel tz)

    toRedState' b tz = replaceRHS $ emptyAttPathInfoFromZipper b tz

    checkReducible (RedFix x) = case x of
      AttAttrSideF Inherited{} AttPathInfo{ attPathList = [] } -> False
      AttAttrSideF{}                                           -> True
      AttLabelSideF{}                                          -> False
      AttBottomLabelSideF                                      -> False

    go x sz = case zoomNextRightOutZipper (checkReducible . toTree) sz of
      Just sz' -> let
          !nsz = modifyTreeZipper reductState sz'
          !nx = f nsz x
        in go nx nsz
      Nothing -> x

    reductState (RedFix x) = case x of
      AttAttrSideF (Synthesized (a, i)) p -> case zoomInIdxPathInfo i p of
        Nothing -> error "Using an over indexed synthesized attribute"
        Just np -> replaceRHS np $ rule (Synthesized a) (toTreeLabel np)
      AttAttrSideF (Inherited a) (AttPathInfo (i:pl) z False) -> case zoomOutRtZipper z of
        Nothing -> replaceRHS (AttPathInfo pl z  True)  $ initialRule (Inherited a)
        Just z' -> replaceRHS (AttPathInfo pl z' False) $ rule (Inherited (a, i)) (toTreeLabel z')
      _ -> error "This state is irreducible"

    replaceRHS p (Fix x) = RedFix $ case x of
      AttAttrSideF a _    -> AttAttrSideF a p
      AttLabelSideF l cs  -> AttLabelSideF l $ replaceRHS p <$> cs
      AttBottomLabelSideF -> AttBottomLabelSideF

runAttReduction :: forall tz syn inh ta la tb lb.
  ( AttConstraint syn inh ta la tb lb, RankedTreeZipper tz
  )
  => AttributedTreeTransducer syn inh ta la tb lb
  -> ReductionStateWithEmptySyn syn inh ta la tb lb tz
  -> ReductionState syn inh ta la tb lb tz
runAttReduction trans istate = toTopTree
  $ buildAttReduction const (either (const errorUnreachable) toZipper istate) trans istate

runAttReductionWithHistory :: forall tz syn inh ta la tb lb.
  ( AttConstraint syn inh ta la tb lb, RankedTreeZipper tz
  )
  => AttributedTreeTransducer syn inh ta la tb lb
  -> ReductionStateWithEmptySyn syn inh ta la tb lb tz
  -> [ReductionState syn inh ta la tb lb tz]
runAttReductionWithHistory trans istate
  = buildAttReduction (\tz -> (. (toTopTree tz:))) id trans istate []

toInitialReductionState :: forall tz syn inh ta la tb lb.
  ( AttConstraint syn inh ta la tb lb, RankedTreeZipper tz
  )
  => AttributedTreeTransducer syn inh ta la tb lb
  -> ta -> ReductionStateWithEmptySyn syn inh ta la tb lb tz
toInitialReductionState trans t = Left (True, toZipper t, attInitialAttr trans)

toInitialAttrState :: forall tz syn inh ta la tb lb.
  ( AttConstraint syn inh ta la tb lb, RankedTreeZipper tz
  )
  => AttAttrEither syn inh -> AttPathInfo tz ta la
  -> ReductionStateWithEmptySyn syn inh ta la tb lb tz
toInitialAttrState (Synthesized a) p = case attPathList p of
  []   ->Left (attIsInitial p, attNonPathZipper p, a)
  i:pl -> Right . RedFix
    $ AttAttrSideF (Synthesized (a, i)) $ p { attPathList = pl }
toInitialAttrState (Inherited a) p = Right . RedFix $ AttAttrSideF (Inherited a) p

fromReductionState ::
  ( AttConstraint syn inh ta la tb lb, RankedTreeZipper tz
  )
  => ReductionState syn inh ta la tb lb tz -> Maybe tb
fromReductionState (RedFix x) = case x of
  AttLabelSideF l cs  -> do
    cs' <- mapM fromReductionState cs
    pure $ mkTreeUnchecked l cs'
  AttBottomLabelSideF -> pure $ mkTreeUnchecked bottomLabel []
  _                   -> Nothing

prettyShowReductionState ::
  ( Show syn, Show inh, Show la, Show lb
  , RtConstraint ta la, RtConstraint tb lb
  , RankedTreeZipper tz
  )
  => ReductionState syn inh ta la tb lb tz -> String
prettyShowReductionState state = go state ""
  where
    go (RedFix x) = prettyShowRhsF
      (\(a, AttPathInfo pl mz b) -> attrShow a pl mz b)
      go x

    attrShow a pl z b = let lShow = labelShow z b in case a of
      Synthesized (a', i) -> S.shows a' . S.shows (i:pl) . S.showString "(" . lShow . S.showString ")"
      Inherited   a'      -> S.shows a' . S.shows pl . S.showString "(" . lShow . S.showString ")"

    labelShow _ True  = S.showString "#"
    labelShow z False = S.shows $ toTreeLabel z


-- A tree transduction for att
instance AttConstraint syn inh ta la tb lb
    => TreeTransducer (AttributedTreeTransducer syn inh ta la tb lb) ta tb where

  treeTrans trans
    =   (toInitialReductionState @RTZipper trans)
    >>> runAttReduction trans
    >>> fromReductionState
    >>> maybe (throwErrorM "This tree transducer is illegal.") pure
