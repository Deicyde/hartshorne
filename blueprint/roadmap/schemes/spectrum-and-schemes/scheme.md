---
declaration: structure
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme
mathlib_file: Mathlib/AlgebraicGeometry/Scheme.lean
---

# Schemes and affine schemes

A scheme is a locally ringed space in which every point has an open
neighbourhood isomorphic to the spectrum of a commutative ring.  Its morphisms
are morphisms of the underlying locally ringed spaces.  A scheme is affine
when it is isomorphic to a spectrum.

Mathlib stores the local-affineness witness in `Scheme`; `IsAffine X` is the
equivalent condition that the canonical map `X → Spec Γ(X,𝒪_X)` is an
isomorphism, with `essImage_Spec` identifying it with Hartshorne's definition.

## Depends on

- [Locally ringed spaces](locally-ringed-space.md)
- [The contravariant Spec functor](spec-functor.md)

## Sources

- [Hartshorne II.2, definition of affine schemes, schemes, and morphisms (p. 74)](../../../sources/hartshorne-ii-2.md#schemes-and-gluing)
