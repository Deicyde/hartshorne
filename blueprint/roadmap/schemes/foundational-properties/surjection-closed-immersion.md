---
article_id: af_4dcdfd3bd74213a9d46395d4
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean
---

# Surjections induce closed immersions

If `φ : A → B` is a surjective ring homomorphism, then
`Spec B → Spec A` is a homeomorphism onto the closed subset
`V(ker φ)`, and the induced structure-sheaf map is surjective.  Thus it is a
closed immersion.

Prime ideals of `B` correspond to primes of `A` containing the kernel.
Localization preserves the required quotient surjections on stalks.  This is
Exercise 2.18(c); `IsClosedImmersion.Spec_iff` records the corresponding affine
classification.

## Depends on

- [The contravariant Spec functor](../spectrum-and-schemes/spec-functor.md)
- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Sources

- [Hartshorne II.2, Exercise 2.18(c), used for closed subschemes on p. 85](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
