# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne, *Algebraic Geometry* (Springer, Graduate Texts in Mathematics 52,
1977), built on Mathlib.

Sections 1 through 4 are decomposed into a dependency graph of 81 formalization
targets, running from the definition of an algebraic set to Theorem I.4.4: the
function field determines a variety up to birational equivalence.

Sections 1 through 3 account for 68 of those targets, ending at Corollary I.3.8,
the arrow-reversing equivalence between affine varieties over `k` and the
finitely generated integral domains over `k`.

**All 68 of them are done**: 67 proved here, sorry-free and on Lean's three standard
axioms, and one already in Mathlib. That covers the whole of §§1–3 as scoped by
the [coverage contract](coverage/README.md), including the results Hartshorne
quotes from commutative algebra rather than proving. The one that took the most
work is Theorem 1.8A(b), the dimension formula `height 𝔭 + dim B/𝔭 = dim B`,
which Hartshorne quotes from Matsumura and which Mathlib does not have in any
form; it is proved here by induction on the height, the height-one case running
through a Noether normalisation and resting on two things Mathlib does have,
that height is preserved by contraction along an integral extension of an
integrally closed domain and that a height-one prime of a unique factorisation
domain is principal.

Section 4, rational maps and birational equivalence, accounts for the remaining
13 targets. It is decomposed but carries no Lean yet.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Coverage](coverage/README.md) — what counts as done, and what is out of
  scope.

Mathlib's algebraic geometry begins at `Spec` and builds schemes; Hartshorne
begins with an affine variety as an irreducible closed subset of `𝔸ⁿ`. The
classical layer has no counterpart upstream, which is why this project targets
Chapter I rather than the scheme theory of Chapters II and III.
