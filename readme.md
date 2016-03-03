[![Master Build Status](https://travis-ci.org/hopper-lang/hopper.svg?branch=master)](https://travis-ci.org/hopper-lang/hopper)
# Hopper: a sound modern language for computation and transactional resource logic

The aim of Hopper is to provide a logically-sound language for describing
ownership, authorization, and transactional interactions thereof. Hopper will
also be a nice language for programming and theorem proving.

Hopper is being designed to support both standalone execution and safe program
execution embedded within a host application (such as
[Juno](https://github.com/buckie/juno)).

## What's where

1. `src/` contains the Haskell implementation.
2. `models/` contains formalizations of semantics, and some design experiments
   that are currently not being used in the implementation.

# Contributing

Awesome, lets talk! We can be found on the `#hopper` channel on freenode.

## Good background reading

* Our core IR is derived from the
  [Types Are Calling Conventions](http://research.microsoft.com/en-us/um/people/simonpj/papers/strict-core/tacc-hs09.pdf)
  paper, which we're augmenting with fancier types.
* As a starting point for combining linear and dependent types, we're drawing
  from [some excellent pre-publication draft work](https://personal.cis.strath.ac.uk/conor.mcbride/pub/Rig.pdf).
* For a good exposition of classical linear logic, see Girard's
  [Linear Logic: its syntax and semantics](http://www.cs.brandeis.edu/~cs112/2006-cs112/docs/girard-intro.pdf).
* For a sketch of pattern matching for linearly-typed data structures, see
  the [Copatterns](http://www2.tcs.ifi.lmu.de/~abel/popl13.pdf) paper.

# Build Guide

Read the [Build Guide](./BuildGuide.md) and if it doesn't work, please file a
ticket that describes any issues you're facing.
