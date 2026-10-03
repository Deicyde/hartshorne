---
declaration: equivalence
origin: bridged
source_units: [chapter-iv-section-4]
---

# Abstract elliptic curves and Weierstrass scheme models

From the general Weierstrass equation of a pointed abstract elliptic curve,
construct Mathlib `WeierstrassCurve` data with invertible discriminant and a
scheme isomorphism from the original curve to the associated projective cubic,
carrying the base point to infinity. Conversely, recover a Chapter IV pointed
elliptic curve from an elliptic Weierstrass model over an algebraically closed
field.

This is a representation bridge; equation data, projective point types, and
the scheme are not treated as definitionally equal.

## Depends on

- [The general Weierstrass equation from a genus-one curve](elliptic-general-weierstrass-equation.md)
- [Affine closed subschemes](../../../schemes/subschemes-and-dimension/affine-closed-subschemes.md)
- [Projective closed subschemes and homogeneous ideals](../../../schemes/projective-sheaves/projective-closed-subscheme-homogeneous-ideal.md)

## Proof depends on

- The pinned `WeierstrassCurve` discriminant and nonsingularity criteria.
- Compatibility of the affine and projective Weierstrass coordinate models.

## Sources

- [Hartshorne IV.4, Proposition 4.6 and proof of Theorem 4.1, pp.319–320](../../../../sources/hartshorne-iv-4.md)
