module Data.Tree.RankedTree.ZipperSpec where

import Test.Hspec

import Control.Monad
import Data.Tree.RankedTree
import Data.Tree.RankedTree.Zipper

spec :: Spec
spec = do

  describe "zooms" $ do
    let treeACCZipper = rtZipper $ TreeA TreeC TreeC

    it "in -> out = id" $ do
      let zoomInOut = zoomInRtZipper >=> zoomOutRtZipper
      zoomInOut treeACCZipper `shouldBe` Just treeACCZipper
      (zoomInRtZipper >=> zoomInOut) treeACCZipper `shouldBe` Nothing

    it "right -> left = id" $ do
      let zoomRightLeft = zoomRightRtZipper >=> zoomLeftRtZipper
      zoomRightLeft treeACCZipper `shouldBe` Nothing
      (zoomInRtZipper >=> zoomRightLeft) treeACCZipper `shouldBe` zoomInRtZipper treeACCZipper

    it "always top" $ do
      zoomTopRtZipper <$> zoomRightRtZipper treeACCZipper `shouldBe` Nothing
      zoomTopRtZipper <$> (zoomInRtZipper >=> zoomRightRtZipper) treeACCZipper `shouldBe` Just treeACCZipper

  describe "others" $ return ()
