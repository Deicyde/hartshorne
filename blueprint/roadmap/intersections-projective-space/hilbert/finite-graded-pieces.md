---
article_id: af_e4e373a8fc28a4a63bcfb288
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.finite_gradedPiece
---

# Finite-dimensional graded pieces

Let $S=k[x_0,\ldots,x_n]$ and let $M$ be a finitely generated
integer-graded $S$-module. Every homogeneous piece $M_d$ is a
finite-dimensional $k$-vector space.

Choose finitely many module generators and replace them by their nonzero
homogeneous components. For fixed $d$, the piece $M_d$ is spanned by
products of these homogeneous generators with the polynomial pieces in the
complementary degrees. Each polynomial piece is finite-dimensional, and
negative complementary degrees contribute zero.

## Depends on

- [The integer grading on a polynomial ring](integer-polynomial-grading.md)
- [Integer-graded module twists](graded-module-twists.md)

## Proof depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)

## Sources

- [Hartshorne I.7, finiteness implicit in the Hilbert-function definition and Theorem 7.5 (p. 51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
