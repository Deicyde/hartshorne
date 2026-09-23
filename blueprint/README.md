# Hartshorne, Algebraic Geometry

A Lean 4 formalization project for classical variety theory in Robin Hartshorne,
*Algebraic Geometry*, scoped to Chapter I §§1–4 and the geometric core of §5
through Theorem 5.3 (§§1–4 on book pp. 1–29 and the §5 core on pp. 31–33).

This scope is decomposed into a dependency graph of 102 formalization targets,
running from the definition of an algebraic set through the properness and
closedness of the singular locus.

Sections 1 through 3 account for 69 of those targets, ending at Corollary I.3.8,
the arrow-reversing equivalence between affine varieties over `k` and the
finitely generated integral domains over `k`.

**All 69 of those targets are done**: 68 proved here, sorry-free and on Lean's
three standard axioms, and one already in Mathlib. This covers §§1–3 in the
[coverage contract](coverage/README.md), including the results Hartshorne
quotes from commutative algebra rather than proving. The one that took the most
work is Theorem 1.8A(b), the dimension formula `height 𝔭 + dim B/𝔭 = dim B`,
which Hartshorne quotes from Matsumura and which Mathlib does not have in any
form; it is proved here by induction on the height, the height-one case running
through a Noether normalisation and resting on two things Mathlib does have,
that height is preserved by contraction along an integral extension of an
integrally closed domain and that a height-one prime of a unique factorisation
domain is principal.

Section 4, rational maps and birational equivalence, accounts for the remaining
17 targets. All are done, ending with the construction and four properties of
the blow-up of affine space at the origin and the birationality of strict
transforms. Altogether, 85 targets are proved here and one is supplied by
Mathlib.

The geometric core of Section 5 contributes 16 further roadmap leaves. Its
regular-local/cotangent-space criterion is an exact Mathlib result, and the
other 15 are now proved here, ending with Theorem 5.3: the singular locus of a
variety is a proper closed subset. Thus all 102 scoped leaves are complete:
100 are proved in this project and two are supplied by Mathlib.

The completion, Cohen-structure, and analytic-isomorphism material later in
§I.5 is deferred. Theorem I.5.7A, the §I.5 exercises, §I.6 onward, and Chapters
II–V are out of scope.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Coverage](coverage/README.md) — what counts as done, and what is out of
  scope.

Mathlib's algebraic geometry begins at `Spec` and builds schemes; Hartshorne
begins with an affine variety as an irreducible closed subset of `𝔸ⁿ`. The
classical layer has no counterpart upstream, which is why this project targets
Chapter I rather than the scheme theory of Chapters II and III.
