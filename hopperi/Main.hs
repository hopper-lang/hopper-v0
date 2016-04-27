{-# LANGUAGE PatternGuards  #-}
module Main where

import Control.Arrow (left)
import Control.Lens
import Control.Monad.STE
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Vector as V
import Text.Parsec (parse)

import Data.HopperException
import System.Console.Haskeline

import Hopper.Internal.Core.Literal
import Hopper.Internal.LoweredCore.ANF (toAnf)
import Hopper.Internal.LoweredCore.ClosureConversion (closureConvert)
import Hopper.Internal.LoweredCore.ClosureConvertedANF
import Hopper.Internal.LoweredCore.EvalClosureConvertedANF as Eval
import Hopper.Internal.Runtime.Heap
import Hopper.Internal.Runtime.HeapRef
import Hopper.Parsing.Term (pExpr)
import Hopper.Parsing.Concrete (concreteToAbstract)

main :: IO ()
main =
  let green = "\ESC[32m\STX"
      red = "\ESC[31m\STX"
      blue = "\ESC[34m\STX"
      end = "\ESC[0m\STX"
      loop :: InputT IO ()
      loop = do
        minput <- getInputLine $ blue ++ "hopper> " ++ end
        case minput of
          Nothing -> return ()
          Just input -> do
            let evaled = hopperEval input
            outputStrLn $ case evaled of
              Left str -> red ++ str ++ end
              Right str -> green ++ str ++ end
            loop

      settings = Settings {
        complete=noCompletion,
        historyFile=Nothing,
        autoAddHistory=True
      }
  in runInputT settings $ withInterrupt loop

hopperEval :: String -> Either String String
hopperEval input = do
  concrete <- left show $ parse pExpr "repl" input
  let abstract = concreteToAbstract concrete

      anf = toAnf abstract

      (ccanf, symbolReg) = closureConvert anf

      startHeap = Heap (Ref 0) Map.empty Map.empty
      envStack = Eval.envStackFromList []
      controlStack = ControlStackEmptyCC
      calculation = evalCCAnf symbolReg envStack controlStack ccanf
      handler (Left err) = Left (handleSTEErr err)
      handler (Right (refVec, CounterAndHeap _ _ _ (Heap _ _ heap))) =
        let ref = V.head refVec
        -- XXX(joel): this could point to an indirection
        in case heap Map.! ref of
          ValueLitCC lit -> Right $ case lit of
            LInteger i -> show i
            LRational r -> show r
            LNatural n -> show n
            LText t -> T.unpack t
          -- TODO show constructor args
          ConstructorCC (ConstrId name) _ -> Right $ T.unpack name
          other -> Left $ show other
  handleSTE handler $ runHeap startHeap 100 calculation


-- We don't actually expect any exceptions in these tests so just use this
-- handler for all of them
--
-- TODO(joel) remove duplication in EvalSpec
handleSTEErr :: SomeHopperException -> String
handleSTEErr she
  | Just err <- she^?_EvalErrorCC = case err of
      HardFaultImpossiblePanicError stack offset step msg filename fileline ->
        unlines
          [ "-- Eval Error (this is bad, bad news) --"
          , ""
          , "Here's what we know:"
          , "> " ++ msg
          , ""
          , unwords ["via", filename, "line", show fileline]
          ]
      _ -> show err
  | Just err <- she^?_HeapError = show err
  | otherwise = "boom boom boom"
