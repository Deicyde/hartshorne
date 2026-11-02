---
article_id: af_b501809e0faea306655db32d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.reducible_plane_curve_bezout
---

# Bézout for reducible plane curves without a common component

Let $Y,Z\subseteq\mathbb P^2$ be projective algebraic sets of dimension
one. Assume that all their irreducible components have dimension one and
that they have no component in common. Then $Y\cap Z$ is finite and

$$\sum_{P\in Y\cap Z}i(Y,Z;P)=\deg Y\,\deg Z.$$

Here $i(Y,Z;P)$ is the pointwise multiplicity defined by summing over
component pairs. Expand the sum, apply the irreducible plane-curve Bézout
theorem to each pair of components, and use the component-degree
identities to factor the resulting finite sums. This is the pure
one-dimensional interpretation of Hartshorne's Remark I.7.8.2.

## Depends on

- [Pointwise multiplicity for reducible plane curves](reducible-plane-curve-pointwise-multiplicity.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)

## Proof depends on

- [Degree of a pure projective curve is the sum of component degrees](pure-projective-curve-degree-components.md)
- [Bézout's theorem for distinct plane curves](plane-curve-bezout.md)

## Sources

- [Hartshorne I.7, Remark 7.8.2 (p. 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
