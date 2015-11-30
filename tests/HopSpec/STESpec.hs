module HopSpec.STESpec (spec) where

import Test.Hspec
import Control.Exception
import Control.Monad.STExcept

spec :: Spec
spec = describe "STE Spec " $ do
  it  "catches errors" $
      Left (ErrorCall "hi")  ==  handleSTE id   (do  throwSTE (ErrorCall "hi") ; return 1 )
  it "returns stuff" $
       (1::Int) == ( either (error "fail") id  $ handleSTE  (id  ::  Either SomeException Int ->  Either SomeException Int ) (return 1))
