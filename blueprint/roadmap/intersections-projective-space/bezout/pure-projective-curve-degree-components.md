---
article_id: af_62bd92ce3f60f2c51058d115
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.projectiveDegree_eq_sum_projectiveComponents
---

# Degree of a pure projective curve is the sum of component degrees

Let $Y\subseteq\mathbb P^2$ be a projective algebraic set of dimension
one whose irreducible components $C$ all have dimension one. Then

$$\deg Y=\sum_C\deg C.$$

Induct on the finite family of components. Distinct components meet in
dimension below one, so the binary union formula applies at each step.
The purity hypothesis ensures that every nonempty partial union has
dimension one and excludes isolated zero-dimensional components.

This states the pure one-dimensional interpretation of Hartshorne's
Remark I.7.8.2, which says “algebraic sets of dimension one.”

## Depends on

- [Projective algebraic sets are finite unions of their components](projective-components-finite-cover.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)

## Proof depends on

- [Degree is additive across a top-dimensional union](degree-union.md)
- [Proper closed subsets of projective varieties have smaller dimension](../dimension/projective-proper-closed-dimension-drop.md)

## Sources

- [Hartshorne I.7, Proposition 7.6(b) and Remark 7.8.2 (pp. 52, 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
