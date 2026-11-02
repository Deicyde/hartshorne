---
article_id: af_b2e49b6cddfde95f6459d6d0
declaration: definition
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.projectiveIntersectionComponentPrimeEquivMinimalPrimes
---

# Projective intersection components correspond to minimal primes

Let $Y$ be a projective variety and let $H$ be a projective algebraic set.
The map $Z\mapsto J(Z)$ identifies the irreducible components of $Y\cap H$
with the homogeneous prime ideals minimal over $J(Y)+J(H)$ whose
projective zero sets are nonempty.

Equivalently, these are the projectively relevant minimal primes over the
annihilator of $S/(J(Y)+J(H))$. The zero set of each corresponding prime
is its component. The nonemptiness condition is essential when the
intersection is empty: the irrelevant ideal may be a minimal prime but
does not represent a projective component.

The projective ideal correspondence turns a homogeneous minimal prime
into a nonempty irreducible closed subset of the intersection. Extend it
to an irreducible component; minimality then forces equality of the
corresponding prime ideals.

## Depends on

- [Intersection multiplicity with a hypersurface](projective-intersection-multiplicity.md)
- [Projective intersection components on an affine chart](../dimension/projective-intersection-components.md)

## Proof depends on

- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)
- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne I.7, minimal-prime/component identification in the proof of Theorem 7.7 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
