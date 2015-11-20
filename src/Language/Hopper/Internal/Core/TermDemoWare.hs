{-# LANGUAGE RankNTypes #-}
module Language.Hopper.Internal.Core.TermDemoWare where
import qualified Language.Hopper.Internal.Core.Term as Tm
import qualified Language.Hopper.Internal.Core.Literal as Lit
-- import qualified  Data.Text as Text
import Data.Text (Text)
-- import qualified
import   Bound as Bd

-- import qualified  Data.Set as Set
import Language.Hopper.Internal.Core.Type

data DemoTerm = V  Text
    | ELit Lit.Literal
    -- | PrimApp Text [a]
    | Force DemoTerm  --- Force is a Noop on evaluate values,
                        --- otherwise reduces expression to applicable normal form
                        -- should force be more like seq a b, cause pure

    | Delay DemoTerm  --- Delay is a Noop on Thunked values, otherwise creates a thunk
                        --- note: may need to change their semantics later?!
    | DemoTerm :@ [DemoTerm]
    | PrimApp  Text [DemoTerm] -- not sure if this is needed, but lets go with it for now

    | Lam [Text]
          DemoTerm
    | Let Text  DemoTerm  DemoTerm
  deriving (Eq,Ord,Read,Show)


-- data DTS a =DTV a
--     | DTLIt Lit.Literal
--     | DTForce (DTS a)  --- Force is a Noop on evaluate values,
--                         --- otherwise reduces expression to applicable normal form
--                         -- should force be more like seq a b, cause pure

--     | DTDelay (DTS a)  --- Delay is a Noop on Thunked values, otherwise creates a thunk
--                         --- note: may need to change their semantics later?!
--     | (DTS a) :?@ [DTS a]
--     | DTPrimApp  String [DTS a] -- not sure if this is needed, but lets go with it for now

--     | DTLam [String]
--           (Scope String DTS a)
--     | DTLet String  (DTS a)  (Scope String DTS a)

demoTerm2ScopedTerm :: DemoTerm -> Tm.Exp () Text
demoTerm2ScopedTerm (V str) = Tm.V $  str
demoTerm2ScopedTerm (ELit l) = Tm.ELit l
demoTerm2ScopedTerm (Force e) = Tm.Force  $ demoTerm2ScopedTerm e
demoTerm2ScopedTerm (Delay e) = Tm.Delay $ demoTerm2ScopedTerm e
demoTerm2ScopedTerm (f :@ lse) = demoTerm2ScopedTerm f Tm.:@ map demoTerm2ScopedTerm lse
demoTerm2ScopedTerm (PrimApp nm ls) = Tm.PrimApp (Lit.PrimopId  nm) (map demoTerm2ScopedTerm ls)
demoTerm2ScopedTerm (Lam args bod) = let dtsBod = demoTerm2ScopedTerm bod
                                       in Tm.Lam  (map (\v -> (v,TVar (),Omega)) args) $  flip  abstract dtsBod (\var -> if  var `elem` args then Just $ var else Nothing)
demoTerm2ScopedTerm (Let nm rhs bod) = Tm.Let (Just nm) Nothing (demoTerm2ScopedTerm rhs) $ flip abstract (demoTerm2ScopedTerm bod) (\var -> if var == nm then Just (Just nm) else Nothing )

newtype PolyF f = PolyF { unPolyF :: forall a . Maybe (f a) }
{-
data PolyF f where
   PF :: (forall a . Maybe (f a)) -> PolyF  f

data ExF f where
  EF :: forall a . (Maybe (f a) -> ExF f)

-}

evaluableDemoTerm :: DemoTerm -> PolyF (Tm.Exp ())
evaluableDemoTerm tm =  PolyF (closed $ demoTerm2ScopedTerm tm)
-- demoTerm2ScopedTerm
