---
article_id: af_e4e373a8fc28a4a63bcfb288
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.finite_gradedPiece
---

# Finite-dimensional graded pieces

Let `S = k[x₀,…,xₙ]` with finitely many variables, and let `M` be a finite
integer-graded `S`-module. Every homogeneous piece `M_d` is a finite-dimensional
`k`-vector space. The sole main declaration is planned as
`Hartshorne.finite_gradedPiece`.

Choose finitely many `S`-module generators and replace them by the finite
collection of all their nonzero homogeneous components. For fixed degree `d`,
the piece `M_d` is spanned by products of those homogeneous generators with
the finitely generated polynomial pieces of the complementary degrees.
Negative complementary degrees contribute zero.

Pinned Mathlib proves `MvPolynomial.homogeneousSubmodule_fg` for finitely many
variables, but it does not lift this fact to the pieces of an arbitrary finite
graded module. This node supplies exactly the finiteness needed for the Hilbert
function; it does not assert that the underlying polynomial ring is
finite-dimensional.

## Depends on

- [The integer grading on a polynomial ring](integer-polynomial-grading.md)
- [Integer-graded module twists](graded-module-twists.md)

## Proof depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)

## Sources

- [Hartshorne I.7, finiteness implicit in the Hilbert-function definition and Theorem 7.5 (p. 51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
