---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsClosedImmersion.Spec_iff
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean
---

# Closed subschemes of an affine scheme

For a morphism `f : X → Spec A`, `f` is a closed immersion if and only if
there is an ideal `I ⊆ A` and an isomorphism
`X ≅ Spec(A/I)` over `Spec A`.

This is exactly `IsClosedImmersion.Spec_iff`. The supporting exact lemma
`IsClosedImmersion.spec_of_quotient_mk` supplies the forward construction from
an ideal: the quotient map is surjective and its spectrum has image `V(I)`.

## Depends on

- [Closed immersions and closed subschemes](closed-immersions.md)
- [The contravariant Spec functor](../spectrum-and-schemes/spec-functor.md)

## Proof depends on

- `IsClosedImmersion.spec_of_quotient_mk`, surjectivity on affine global
  sections, and the first isomorphism theorem.

## Sources

- [Hartshorne II.3 (subschemes-and-dimension)](../../../sources/hartshorne-ii-3.md#subschemes-and-dimension)
