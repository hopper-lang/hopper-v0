{-# LANGUAGE TypeOperators #-}
module Language.Hopper.Internal.Core.GTerm where


import Data.Functor.Coproduct
import Data.Functor.Identity
import Data.Text
import Bound.Scope.Simple

data PrimOpId = PID Int

data ConId = ConId !Text
data GLet rhsg bodf a = GLet (Maybe Text) (rhsg a) (Scope (Maybe Text) bodf a )

data GComp f a = GApp (f a) [f a]
                | GPrimApp PrimOpId  [f a]
                | GReturn (f a)
                | GSeqThunk (f a) (f a)


data GAllocEnvCaptureHL f a = GHLLambda [Text] (Scope Text f a) | Delay (f a)

data GAllocFirstOrder f a = ConstrApp ConId [f a] | GLit


data Literal a = LitInt Int


-- newtype Exp a = Exp
--                   ((
--                     (GLet Exp Exp ) `Coproduct` (
--                     (GComp Exp) `Coproduct`
--                     (Literal))) a
--         )

data Exp a  = ExpLet (GLet Exp Exp a)
              | ExpComp (GCompHL Exp a) |  ExpLit (Literal a)


data ANF a = ANFLet (GLet (GCompHL Identity `Coproduct` Literal) ANF a)
            |  ANFTailCall (GCompHL Identity a)


-- newtype ANF a = ANF (
--       ((GLet (GComp Identity `Coproduct` Literal)
--                   ANF) `Coproduct`
--       (GComp Identity)
--                    ) a
--     )
