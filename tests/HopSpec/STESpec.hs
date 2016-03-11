{-#  LANGUAGE TypeOperators #-}
module HopSpec.STESpec (spec) where

import Test.Hspec
import Control.Exception
import Control.Monad.STE
import Data.Hop.Or

spec :: Spec
spec = describe "STE Spec " $ do
  it  "catches errors" $
      Left (InR "hi")  ==  handleSTE (id :: Either ((():+ () ):+ String) Int -> Either ((():+ () ):+ String) Int )   (do extendError $ throwSTE ( InR "hi") ; return 1 )
  it "returns stuff" $
       (1::Int) == ( either (error "fail") id  $ handleSTE  id  (return 1))
