{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.Decompose.SmttToSatt where

import           SattPrelude

import           Control.Monad.State
import qualified Data.HashMap.Strict        as HashMap
import qualified Data.HashSet               as HashSet
import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import qualified Data.Tree.Trans.SATT       as SATT
import qualified Data.Tree.Trans.SMAC       as SMAC
import           Data.Tree.Trans.Stack
import qualified Data.Tree.Trans.TOP        as TOP
import qualified Data.Vector                as V

data ContextParamToken = ContextParamToken
  { contextParamIdx :: RankNumber
  , contextStackIdx :: (Bool, RankNumber)
  } deriving (Eq, Ord, Show, Generic)

instance Hashable ContextParamToken

type SubstitutionLabelIndex
  = Vector (HashMap RankNumber [(Bool, RankNumber)])

data SubstitutionTreeF tb lb idx a
  = OriginalOutputLabelF lb
  | StackExprLabelF StackExprLabel
  | ContextParamF ContextParamToken
  | SubstitutionF idx (NodeVec a)
  deriving (Eq, Show, Generic, Generic1, Functor, Foldable)

instance (Hashable lb, Hashable idx, Hashable a) => Hashable (SubstitutionTreeF tb lb idx a)

deriveEq1 ''SubstitutionTreeF
deriveShow1 ''SubstitutionTreeF

type instance Element (SubstitutionTreeF tb lb idx a) = a

instance MonoFoldable (SubstitutionTreeF tb lb idx a)

type SubstitutionTree tb lb = Fix (SubstitutionTreeF tb lb SubstitutionLabelIndex)


instance RankedTree (SubstitutionTree tb lb) where
  type LabelType (SubstitutionTree tb lb)
    = SubstitutionTreeF tb lb SubstitutionLabelIndex ()

  treeLabel (Fix x) = void x
  treeChilds (Fix x) = fromList $ toList x

  treeLabelRank _ = length

  mkTreeUnchecked x cs = Fix $ case x of
    OriginalOutputLabelF l -> OriginalOutputLabelF l
    StackExprLabelF s      -> StackExprLabelF s
    ContextParamF c        -> ContextParamF c
    SubstitutionF i _      -> SubstitutionF i cs


-- FIXME: give the implentation
checkNonCopying :: MonadThrow m
  => SMAC.StackMacroTreeTransducer s ta la tb lb -> m ()
checkNonCopying _ = pure ()

-- | decompose a non-copying smtt to a tdtt and an single-use satt
--
-- Examples:
-- >>> import Data.Tree.RankedTree.Label
-- >>> import Data.Tree.Trans.SMAC.Instances
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
--
decomposeSmttNC :: forall m s ta la tb lb.
  ( SMAC.SmttConstraint s ta la tb lb
  , Eq lb, Hashable lb
  , MonadThrow m
  )
  => SMAC.StackMacroTreeTransducer s ta la tb lb
  -> m
    ( TOP.TdttTransducer s ta (SubstitutionTree tb lb)
    , SATT.SattTransducer () RankNumber (SubstitutionTree tb lb) tb
    )
decomposeSmttNC transNoST = do
    checkNonCopying trans
    pure $ fromMaybe errorUnreachable $ (,)
      <$> TOP.buildTdtt ie1 rules1
      <*> SATT.buildSatt ia2 irules2 rules2
  where
    trans = SMAC.toStandardForm transNoST

    treeLabelRankTb = treeLabelRank (Proxy @tb)

    insertSubstLabel = modify' . first . insertSet
    updateMaxRank = modify' . second . max

    substitutionIdx tokens l cs =
      ( join tokens
      , TOP.TdttLabelSide
        (SubstitutionF tokens $ replicate (length cs + 1) ())
        $ l `cons` cs
      )

    traverseRHSStk s = case s of
      SMAC.SmttContext{}     -> traverseRHSTail True 0 s
      SMAC.SmttState f u cs  -> let
          (tokens, cs') = unzip $ traverseRHSStk <$> cs
        in substitutionIdx tokens (TOP.tdttState f u) cs'
      SMAC.SmttStackEmpty    ->
        ( []
        , TOP.TdttLabelSide (StackExprLabelF $ StackedExpr StackEmptyF) []
        )
      SMAC.SmttStackTail{}   -> traverseRHSTail True 0 s
      SMAC.SmttStackCons v' s' -> let
          (tokensV, v'') = traverseRHSVal v'
          (tokensS, s'') = traverseRHSStk s'
        in substitutionIdx [tokensV, tokensS]
          (TOP.TdttLabelSide (StackExprLabelF $ StackedExpr $ StackConsF () ()) [])
          [v'', s'']

    traverseRHSVal v = case v of
      SMAC.SmttLabelSide l cs -> let
          (tokens, cs') = unzip $ traverseRHSVal <$> cs
        in substitutionIdx tokens
          (TOP.TdttLabelSide (OriginalOutputLabelF l) [])
          cs'
      SMAC.SmttStackBottom ->
        ( []
        , TOP.TdttLabelSide (StackExprLabelF $ ValuedExpr StackBottomF) []
        )
      SMAC.SmttStackHead s -> traverseRHSTail False 0 s

    traverseRHSTail b i s = case s of
      SMAC.SmttStackTail s' -> traverseRHSTail b (i + 1) s'
      SMAC.SmttContext c    -> let
          cxtToken = ContextParamToken c (b, i)
        in
          ( [cxtToken]
          , TOP.TdttLabelSide (ContextParamF cxtToken) []
          )
      _  -> let
          (tokens, s') = traverseRHSStk s
          substIdx l = snd . substitutionIdx [tokens] (TOP.TdttLabelSide (StackExprLabelF l) []) . singleton
          f = if b
            then id
            else substIdx (ValuedExpr $ StackHeadF ())
        in
          (tokens,) $ f $ stimesEndo i
            (substIdx $ StackedExpr $ StackTailF ())
            s'

    buildIndex idx = let
        go tokens = sortWith snd <$> foldr
          (\(ContextParamToken c (b, i)) -> insertWith (<>) c [(b, i)])
          HashMap.empty tokens
      in go <$> idx

    collectRhs rhs = case rhs of
      TOP.TdttState s u      -> do
        updateMaxRank $ labelRank s
        pure $ TOP.tdttState s u
      TOP.TdttLabelSide l cs ->
        let
          l' = case l of
            SubstitutionF idx cs'   -> SubstitutionF (buildIndex idx) cs'
            OriginalOutputLabelF ol -> OriginalOutputLabelF ol
            StackExprLabelF s       -> StackExprLabelF s
            ContextParamF c         -> ContextParamF c
        in do
          insertSubstLabel l'
          updateMaxRank $ length cs
          TOP.TdttLabelSide l' <$> traverse collectRhs cs
      TOP.TdttBottomLabelSide -> pure TOP.TdttBottomLabelSide

    buildRhs rhs = let
        (_, idxRhs) = traverseRHSStk rhs
      in collectRhs idxRhs

    ((ie1, rules1), (ls, mr)) = flip runState (HashSet.empty, 0) $ do
      ie <- buildRhs $ SMAC.smttInitialExpr trans
      rules <- traverse (\((f, l), rhs) -> (f, l, ) <$> buildRhs rhs)
        $ mapToList $ SMAC.smttTransRules trans
      pure (ie, rules)

    ia2 = ()
    irules2 = [(SATT.Synthesized (), SATT.SynAttrSide () 0)]
    rules2
      =  [ (SATT.Synthesized (), l, h l) | l <- setToList ls ]
      <> do
        l <- setToList ls
        (idx, p) <- case l of
          SubstitutionF idx cs -> [(idx, length cs - 1)]
          _                    -> []

        j <- [0..(mr - 1)]
        i <- [0..p]

        pure
          ( SATT.Inherited (j, i), l
          , if i == 0 && j < p
            then SATT.SynAttrSide () $ j + 1
            else buildSattInheritedRules
              (SATT.InhAttrSide j) 0 (fromMaybe [] $ lookup j $ idx `indexEx` i)
          )

    buildSattInheritedRules _  _ []
      = SATT.SattStackEmpty
    buildSattInheritedRules yj n [(True, i)]
      = stimesEndo (n - i) (SATT.SattStackCons SATT.SattStackBottom)
      $ stimesEndo i SATT.SattStackTail yj
    buildSattInheritedRules yj n ((False, i):xs)
      = stimesEndo (n - i) (SATT.SattStackCons SATT.SattStackBottom)
      $ SATT.SattStackCons (SATT.SattStackHead $ stimesEndo i SATT.SattStackTail $ yj)
      $ buildSattInheritedRules yj (i + 1) xs
    buildSattInheritedRules _ _ _ = error "not sorted context"

    h (OriginalOutputLabelF l) = SATT.SattStackCons
      ( SATT.SattLabelSide l
      $ V.generate (treeLabelRankTb l) (SATT.SattStackHead . SATT.InhAttrSide)
      )
      SATT.SattStackEmpty
    h (StackExprLabelF (ValuedExpr l)) = case l of
      StackBottomF{} -> SATT.SattStackEmpty
      StackHeadF{}   -> SATT.SattStackCons
        (SATT.SattStackHead $ SATT.InhAttrSide 0)
        SATT.SattStackEmpty
    h (StackExprLabelF (StackedExpr l)) = case l of
      StackEmptyF{} -> SATT.SattStackEmpty
      StackTailF{}  -> SATT.SattStackTail (SATT.InhAttrSide 0)
      StackConsF{}  -> SATT.SattStackCons
        (SATT.SattStackHead (SATT.InhAttrSide 0))
        (SATT.SattStackTail (SATT.InhAttrSide 1))
    h (ContextParamF c) = case c of
      ContextParamToken i (False, j) -> SATT.SattStackCons
        ( SATT.SattStackHead
        $ stimesEndo i SATT.SattStackTail
        $ SATT.InhAttrSide j
        )
        SATT.SattStackEmpty
      ContextParamToken j (True,  i) ->
        stimesEndo i SATT.SattStackTail
        $ SATT.InhAttrSide j
    h SubstitutionF{}              = SATT.SynAttrSide () 0
