module Data.Tree.Trans.Decompose.SmttToSatt where

import           SattPrelude

import           Data.Tree.RankedTree
import qualified Data.Tree.Trans.SATT  as SATT
import qualified Data.Tree.Trans.SMAC  as SMAC
import qualified Data.Tree.Trans.TOP  as TOP
import qualified Data.Vector          as V

data SubstitutionTreeF tb lb a
  = OriginalOutputLabelF lb
  | ContextParamF RankNumber
  | SubstitutionF (NodeVec a)
  deriving (Eq, Ord, Show, Generic, Generic1, Functor, Foldable)

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
-- >>> (trans1, trans2) = decomposeSmttNC sampleSmtt
-- >>> treeTrans trans2 <=< treeTrans trans1 $ inputSampleTree
-- D(F,F)
-- >>> (==) <$> (treeTrans trans2 <=< treeTrans trans1 $ inputSampleTree) <*> treeTrans sampleSmtt inputSampleTree
-- True
--
decomposeSmttNC :: forall s ta la tb lb.
  ( SMAC.SmttConstraint s ta la tb lb
  , Eq lb, Hashable lb
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
    trans = toStandardForm transNoST

    ((ie1, rules1), _) = undefined


    ia2 = ()
    irules2 = undefined
    rules2 = undefined
