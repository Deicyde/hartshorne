---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Spec.fullyFaithful
mathlib_file: Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean
---

# Spec is fully faithful

For commutative rings `A` and `B`, every locally-ringed-space morphism
`Spec B → Spec A` is induced by a unique ring homomorphism `A → B`.
Equivalently, the contravariant Spec functor is fully faithful.

Take global sections to recover the ring map, use locality of each stalk map
to identify the underlying point map with inverse image of primes, and then
identify the sheaf map.  This is Proposition 2.3(c).

## Depends on

- [Global sections of Spec](spec-global-sections.md)
- [The contravariant Spec functor](spec-functor.md)

## Sources

- [Hartshorne II.2, Proposition 2.3(c) and Caution 2.3.0 (pp. 73–74)](../../../sources/hartshorne-ii-2.md#locally-ringed-spaces-and-proposition-23)
