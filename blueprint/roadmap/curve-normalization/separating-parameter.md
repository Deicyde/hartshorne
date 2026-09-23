---
article_id: af_cdd991fa7124477bed654f2a
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-normalization]
---

# One-dimensional function fields have separating parameters

Let `K/k` be an essentially finitely generated field extension of
transcendence degree one, with `k` algebraically closed. There is a
transcendental element `t : K` such that `K/k(t)` is finite and separable.

In Lean, take `k(t)` to be `IntermediateField.adjoin k {t}` and expose the
`FiniteDimensional` and `Algebra.IsSeparable` instances used by normalization.
The existing separating-transcendence-basis theorem, formalizing the Theorem
4.8A route over the perfect field `k`, produces a finite basis of cardinality
one. Extract its unique element and identify its generated intermediate field
with `k(t)`. This is a project-added replacement for Hartshorne's arbitrary
nonconstant parameter in the proof of Lemma 6.5; it is what allows the
geometric branch to use Mathlib's separable normalization theorems.

The same conclusion holds for `t⁻¹`, since `k(t⁻¹) = k(t)`. Record this
equality explicitly so the two-chart construction does not repeat field-tower
bookkeeping.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Separably generated field extensions](../rational-maps/separably-generated.md)

## Sources

- [Hartshorne I.4, Theorem 4.8A (p. 27)](../../sources/hartshorne.md#i4)
- [Hartshorne I.6, one-dimensional function fields in the proof of Lemma 6.5 (p. 41)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
