module Hopper.Internal.Core.DataTypes where

data IndexedDesc
  = Pi s (

data MutualDefn = MutualDefn
  [(Name, InductiveDefn)]
  [(Name, CoinductiveDefn)]
  [(Name, FunctionDefn)]
