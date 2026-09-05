# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne, *Algebraic Geometry* (Springer, Graduate Texts in Mathematics 52,
1977), built on Mathlib.

Sections 1 through 3 are decomposed into a dependency graph of 53 formalization
targets, running from the definition of an algebraic set to Corollary I.3.8: the
functor sending an affine variety to its coordinate ring is an arrow-reversing
equivalence onto the finitely generated integral domains over `k`.

42 of them are done: 41 proved here, sorry-free and on Lean's three standard
axioms, and one already in Mathlib. The progress page has the current count and
the graph shows which of the remaining eleven are blocked and by what.
The largest remaining gap is the dimension formula
`height 𝔭 + dim B/𝔭 = dim B`, the second clause of Hartshorne's Theorem 1.8A,
which he quotes from Matsumura and which Mathlib does not have in any form.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Coverage](coverage/README.md) — what counts as done, and what is out of
  scope.

Mathlib's algebraic geometry begins at `Spec` and builds schemes; Hartshorne
begins with an affine variety as an irreducible closed subset of `𝔸ⁿ`. The
classical layer has no counterpart upstream, which is why this project targets
Chapter I rather than the scheme theory of Chapters II and III.
