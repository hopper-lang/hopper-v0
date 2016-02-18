module HopSpec.STESpec (spec) where

import Test.Hspec
import Control.Exception
import Control.Monad.STE

spec :: Spec
spec = describe "STE Spec " $ do
  it  "catches errors" $
      Left  "hi"  ==  handleSTE id   (do  throwSTE ( "hi") ; return 1 )
  it "returns stuff" $
       (1::Int) == ( either (error "fail") id  $ handleSTE  id  (return 1))
