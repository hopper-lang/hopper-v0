module HopSpec.LiteralSpec
  ( spec
  ) where

import Test.Hspec
import Hopper.Internal.Core.Literal

spec :: Spec
spec = describe "Literal evaluation" $ do
  describe "integerLog" $ do
    it "returns the number of bits in an Integral value" $
      11 == integerLog 1024
    it "doesn't break for 0" $
      1 == integerLog 0
