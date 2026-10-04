# Hartshorne, Algebraic Geometry

A Lean 4 formalization project for classical variety theory in Robin Hartshorne,
*Algebraic Geometry*, scoped to Chapter I §§1–4, the geometric core of §5
through Theorem 5.3, and §6 through Corollary 6.12.

The accepted dependency graph has 163 targets, all fully formalized: 159 are
proved in this project and four are supplied by Mathlib. The first 114 run from
the definition of an algebraic set through the local structure of nonsingular
curves through Lemma 6.4; the next 26 prove normalization and the
valuation-space results through Proposition 6.7; the final 23 construct
projective models and the curve/function-field category equivalence.

The completed §I.7 milestone has 50 formalized targets for intersection
dimensions, graded Hilbert theory, projective degree, and Bézout. The derived
progress views report the current aggregate without duplicating it here.

The completed core of Sections 1 through 3 accounts for 69 of those targets,
ending at Corollary I.3.8, the arrow-reversing equivalence between affine
varieties over `k` and the finitely generated integral domains over `k`.
Theorem I.3.9A is part of the new normalization milestone below.

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

The completed main-text scope of Section 4, rational maps and birational
equivalence, accounts for the remaining 17 targets, ending with the blow-up of
affine space at the origin. The weak consequence of Exercise 4.8(a) newly
needed by Proposition 6.7 is now formalized in the normalization milestone.

The geometric core of Section 5 contributes 16 further roadmap leaves. Its
regular-local/cotangent-space criterion is an exact Mathlib result, and the
other 15 are now proved here, ending with Theorem 5.3: the singular locus of a
variety is a proper closed subset. Thus all 102 scoped leaves are complete:
100 are proved in this project and two are supplied by Mathlib.

The opening of Section 6 through Lemma 6.4 contributes 12 leaves. Mathlib
supplies the two clauses of Theorem 6.1A exactly; the ten project leaves develop
the DVR local rings of nonsingular curves and prove that inclusion of local
rings inside the function field determines the point. All 12 are complete, so
the completed portion has 110 project formalizations and four Mathlib results.

The completed normalization milestone adds 26 leaves. It includes the exact nonseparable
Theorems 3.9A and 6.3A, proves finite poles and realizes every function-field
DVR on a nonsingular affine curve, then constructs the valuation-space curve
and reaches Proposition 6.7. All 26 leaves are formalized, including the
abstract curve's function field and the isomorphism from every nonsingular
quasi-projective curve to its open valuation-space image.

The completed 23-leaf milestone adopts Exercise 3.3(b),(c), exposes the
valuation and local-ring bridges needed by Proposition 6.8, constructs the
nonsingular projective model of a one-dimensional function field in Theorem
6.9, and decomposes Corollaries 6.10–6.12. Its two-chart diagonal construction
uses the existing separable normalization charts but imposes no separability
hypothesis on the function field.

Apart from the regularity-under-completion clause of Theorem I.5.4A used in
V.5, the remaining completion, Cohen-structure, and analytic-isomorphism
material later in §I.5 is deferred. Section I.7 has a fine DAG, §I.8 has a claim-by-claim
survey disposition, and all of Chapter II has a 444-leaf fine DAG with 99 exact
pinned-Mathlib results. All of Chapter III has a 288-leaf fine roadmap with
nineteen exact Mathlib results. All of Chapter IV has a 201-leaf fine roadmap with
two exact Mathlib results, plus five reactivated earlier-exercise prerequisites.
All of Chapter V has a 230-leaf fine roadmap with one exact Mathlib result,
plus two reactivated III.7 prerequisites, one II.8 prerequisite, two I.5
prerequisites, and one Appendix A HRR prerequisite. Appendix A has a 72-leaf
fine roadmap, Appendix B a 69-leaf fine roadmap, and Appendix C a 69-leaf fine
roadmap with one exact pinned-Mathlib foundation. Reference apparatus,
Appendix C's history and terminal exercises, and already-dispositioned
non-target material remain out of scope.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Remaining-book roadmap](roadmap/remaining-book/README.md) — the completed
  source and dependency-DAG sequencing from §I.8 through Appendix C.
- [Coverage](coverage/README.md) — what counts as done, and what is out of
  scope.

Mathlib's algebraic geometry begins at `Spec` and builds schemes; Hartshorne
begins with an affine variety as an irreducible closed subset of `𝔸ⁿ`. The
classical layer has no counterpart upstream, which is why the completed Lean
scope starts in Chapter I. Later formalization work should reuse exact Mathlib
results recorded by the roadmap instead of restating them.
