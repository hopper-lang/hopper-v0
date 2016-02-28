module HopSpec.LiteralSpec
  ( spec
  ) where

import Test.Hspec
import Hopper.Internal.Core.Literal

spec :: Spec
spec = describe "Literal evaluation" $ do
  describe "integerLog" $ do
    it "returns the number words in an Integer value" $
      2 == integerLimbSize 1000000000000000000024
    it "doesn't break for 0" $
      1 == integerLimbSize 0
