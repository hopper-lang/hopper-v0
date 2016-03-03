# How can I build this?

## Building with Cabal

  1) make sure you have a GHC installed and in your path whose reported `ghc --version` matches
one of the configurations listed in the tested-with field of the `hopper.cabal` file.
  2) have an up to date version of cabal-install installed.
  3) `cabal update ; cabal install`
  4) done!

## Building with Stack

Run `stack build`.

## I had a build failure despite following these directions!

Check that you're using the most up-to-date version of `cabal-install` and
that the GHC version you're using is listed in the `Tested-with` field of the
`hopper.cabal` file. If despite this you have a build failure (whether of the
build plan or the build itself), please file a GitHub issue with the error
message and any specifics of your system configuration and version information!
