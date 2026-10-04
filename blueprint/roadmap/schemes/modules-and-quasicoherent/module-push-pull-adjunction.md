---
article_id: af_a10e68c7ff360c43ea9f3e53
declaration: def
origin: cited
source_units: [chapter-ii-section-5]
mathlib: true
mathlib_declaration: SheafOfModules.pullbackPushforwardAdjunction
mathlib_file: Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean
---

# Pushforward, pullback, and their adjunction

For a morphism of ringed spaces `f : (X,O_X) ⟶ (Y,O_Y)`, define the module
pushforward `f_*` by giving the ordinary direct image its `O_Y`-action through
`f#`.  Define module pullback by extension of scalars,
`f*G = f⁻¹G ⊗[f⁻¹𝒪_Y] 𝒪_X`, and prove the natural adjunction

`Hom_X(f*G, F) ≃ Hom_Y(G, f_*F)`.

Mathlib's site-level `SheafOfModules.pullback`, `pushforward`, and named
adjunction are the exact categorical realization; scheme morphisms specialize
that construction.

## Depends on

- [Tensor products of module sheaves](module-tensor-product.md)
- [Direct image of a sheaf](../sheaf-functors/direct-image.md)
- [Inverse image of a sheaf](../sheaf-functors/inverse-image.md)

## Proof depends on

- [Inverse image is left adjoint to direct image](../sheaf-functors/inverse-direct-adjunction.md)
- Extension–restriction of scalars for modules.

## Sources

- [Hartshorne II.5, direct and inverse images on printed pp. 109–110](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
