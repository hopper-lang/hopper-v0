# How can i build this?
  1) make sure you have a GHC installed and in your path whose reported `ghc --version` matches
one of the configurations listed in the tested-with field of the `hopper.cabal` file.
  2) have an up to date version of cabal-install installed.
  3) `cabal update ; cabal install`
  4) done!

## I had a build failure despite following these directions!
Check that you're using the most up to date version of cabal-install and
that the GHC version you're using is listed in the Tested-with field of the
Hopper cabal file. If despite this you have a build failure
(whether of the build plan or the build itself), please file an issue ticket
and report the error message along with your system configuration and version
information!


## Can I use stack to build this?
No, we do not provide user facing support for using the stack build facilities,
we only have that as a convenience for the members of the development team who
are using stack for their personal development environment. If you really want
help with stack, ask Brian really nicely.
