# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne, *Algebraic Geometry* (Springer, Graduate Texts in Mathematics 52,
1977), built on Mathlib.

Sections 1 through 3 are decomposed into a dependency graph of 44 formalization
targets, running from the definition of an algebraic set to Corollary I.3.8: the
functor sending an affine variety to its coordinate ring is an arrow-reversing
equivalence onto the finitely generated integral domains over `k`. Nothing is
proved yet.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Coverage](coverage/README.md) — what counts as done, and what is out of
  scope.

Mathlib's algebraic geometry begins at `Spec` and builds schemes; Hartshorne
begins with an affine variety as an irreducible closed subset of `𝔸ⁿ`. The
classical layer has no counterpart upstream, which is why this project targets
Chapter I rather than the scheme theory of Chapters II and III.
