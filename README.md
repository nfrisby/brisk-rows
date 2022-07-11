# Intro

This repository contains some hobby programming I've recently done.
I'm sharing it so that I can attract feedback and collaborators.
If we find some interesting use cases and the library can perform well there, then I hope to propose it internally for Tweag to develop&maintain.

# `BriskRows`

The `brisk-rows` package is a proof-of-concept library for Haskell _row types_.

It is an exploration of the question: how usable can a row types library be without relying on a typechecker plugin?
The package does already include a plugin, but that's ultimately only for convenience.

Priorities:

- GHC's structural equivalence suffices at kind `ROW`: row type equivalence does not depend on the order in which columns were inserted/deleted.

- The user cannot break invariants without importing `BriskRows.Internal`.

- GHC will not infer a type with a column type variable or a row type variable.
  This is a compromise: we lose expressivity in order to avoid illegible/overwhelming type errors.
  A library that fundamentally relied on a more sophisticated typechecker plugin wouldn't require this compromise: proper row polymorphism already avoids illegible/overwhelming type errors.
  However, this library intentionally does not rely on such a plugin, and so we eschew proper row polymorphism in favor of legible/minimal type errors.

# Tour

Be advised: the documentation is hit and miss so far.

I designed/implemented this against GHC 8.10.7; that's just what's on my machine.
The non-plugin code does compile with GHC HEAD.

_All_ of the main logic is in `brisk-rows:BriskRows.Internal`.

You can see some examples in `brisk-rows-test:Test`.
