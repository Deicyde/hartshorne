---
article_id: af_62bd92ce3f60f2c51058d115
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
---

# Degree of a pure projective curve is the sum of component degrees

Let `Y ⊆ ℙ²` be a projective algebraic set with `projDim Y = 1` whose
irreducible components all have projective dimension one.  Then

`projectiveDegree Y = ∑ C ∈ projectiveComponents Y, projectiveDegree C`.

The unique main declaration is planned as
`Hartshorne.projectiveDegree_eq_sum_projectiveComponents`.

Induct over the finite component family.  Distinct irreducible components meet
in dimension strictly below one, so the binary union formula applies at each
step.  The explicit ambient dimension hypothesis is the Lean interface for the
phrase *pure one-dimensional* and makes every nonempty partial union have
dimension one by monotonicity. Hartshorne's Remark 7.8.2 literally says
"algebraic sets of dimension one." The componentwise degree identity needs the
stated purity hypothesis to exclude isolated zero-dimensional components, so
this article records an explicit bridged strengthening rather than attributing
that wording verbatim to Hartshorne.

## Depends on

- [Projective algebraic sets are finite unions of their components](projective-components-finite-cover.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)

## Proof depends on

- [Degree is additive across a top-dimensional union](degree-union.md)
- [Proper closed subsets of projective varieties have smaller dimension](../dimension/projective-proper-closed-dimension-drop.md)

## Sources

- [Hartshorne I.7, Proposition 7.6(b) and Remark 7.8.2 (pp. 52, 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
