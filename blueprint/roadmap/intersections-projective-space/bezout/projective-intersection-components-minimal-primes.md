---
article_id: af_b2e49b6cddfde95f6459d6d0
declaration: definition
origin: bridged
source_units: [chapter-i-section-7-main]
---

# Projective intersection components correspond to minimal primes

Let `Y` be a projective variety and `H` a projective algebraic set. The map

`Z ↦ J(projectiveComponentCarrier Z)`

identifies the irreducible components of `Y ∩ H` with the homogeneous prime
ideals minimal over `J(Y) + J(H)`. Equivalently, it identifies them with the
minimal primes over the annihilator of the intersection module
`S/(J(Y)+J(H))`. For each component, the projective zero set of its attached
prime is exactly its component carrier.

The main declaration is planned as a noncomputable equivalence
`Hartshorne.projectiveIntersectionComponentPrimeEquivMinimalPrimes`, with the
zero-set identity exposed as a supporting theorem. The forward minimality is
already available from the intersection-multiplicity construction. The
converse takes a homogeneous minimal prime, uses the projective ideal
correspondence to obtain a nonempty irreducible closed subset of `Y ∩ H`, and
extends it to a unique irreducible component; minimality forces equality of
the attached prime ideals.

## Depends on

- [Intersection multiplicity with a hypersurface](projective-intersection-multiplicity.md)
- [Projective intersection components on an affine chart](../dimension/projective-intersection-components.md)

## Proof depends on

- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)
- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne I.7, minimal-prime/component identification in the proof of Theorem 7.7 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
