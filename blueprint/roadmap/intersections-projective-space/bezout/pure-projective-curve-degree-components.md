---
article_id: af_62bd92ce3f60f2c51058d115
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
---

# Degree of a pure projective curve is the sum of component degrees

Let `Y ⊆ ℙ²` be a projective algebraic set whose irreducible components all
have projective dimension one.  Then

`projectiveDegree Y = ∑ C ∈ projectiveComponents Y, projectiveDegree C`.

Induct over the finite component family.  Distinct irreducible components meet
in dimension strictly below one, so the binary union formula applies at each
step.  The empty component family supplies the empty-set base case.

## Depends on

- [Projective algebraic sets are finite unions of their components](projective-components-finite-cover.md)
- [Degree is additive across a top-dimensional union](degree-union.md)

## Proof depends on

- [Proper closed subsets of projective varieties have smaller dimension](../dimension/projective-proper-closed-dimension-drop.md)

## Sources

- [Hartshorne I.7, Proposition 7.6(b) and Remark 7.8.2 (pp. 52, 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
