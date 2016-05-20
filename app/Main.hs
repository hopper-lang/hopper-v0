module Main where

import qualified Data.Vector as V

import Hazel

swap, illTyped, diagonal :: Value

swap = Lam (Let
  (MatchTuple (V.fromList [MatchVar UseOnce, MatchVar UseOnce]))
  (BVar 0)
  (Prd (V.fromList [Neu (BVar 1), Neu (BVar 0)]))
  )

illTyped = Let
  (MatchTuple (V.fromList [MatchVar UseOnce, MatchVar UseOnce]))
  (Annot (Lam (Neu (BVar 0))) (LollyTy (PrimTy NatTy) (PrimTy NatTy)))
  (Prd (V.fromList [Neu (BVar 0), Neu (BVar 1)]))

diagonal = Lam (Prd (V.fromList [Neu (BVar 0), Neu (BVar 0)]))

caseExample :: Computation
caseExample = Case
  (Annot (Label "x") (LabelsTy (V.fromList ["x", "y"])))
  (V.fromList ["x", "y"])
  (PrimTy NatTy)
  (V.fromList
    [ Primitive (Nat 1)
    , Primitive (Nat 2)
    ]
  )

caseExample' :: Value
caseExample' = Neu caseExample

primopExample :: Computation
primopExample =
  let pair :: Value -> Value -> Value
      pair x y = Prd (V.fromList [x, y])
  in App (Annot (Primop ConcatString) (inferPrimop ConcatString))
         (pair (StrV "abc") (StrV "xyz"))

main :: IO ()
main = do
  -- this typechecks
  let swapTy =
        let x = PrimTy StringTy
            y = PrimTy NatTy
        in LollyTy (TupleTy (V.fromList [x, y])) (TupleTy (V.fromList [y, x]))
  putStrLn "> checking swap"
  putStrLn $ runChecker $ checkToplevel swapTy swap


  -- but this doesn't -- it duplicates its linear variable
  let diagonalTy =
        let x = PrimTy StringTy
        in LollyTy x (TupleTy (V.fromList [x, x]))
  putStrLn "> checking diagonal (expected failure due to duplicating linear variable)"
  putStrLn $ runChecker $ checkToplevel diagonalTy diagonal

  putStrLn "> checking case"
  putStrLn $ runChecker $ checkToplevel (PrimTy NatTy) caseExample'
  print $ evalC [] caseExample

  putStrLn "> checking primop"
  putStrLn $ runChecker $ checkToplevel (PrimTy StringTy) (Neu primopExample)
  print $ evalC [] primopExample
