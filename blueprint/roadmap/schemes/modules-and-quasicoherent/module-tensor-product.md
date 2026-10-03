---
declaration: definition
origin: cited
source_units: [chapter-ii-section-5]
---

# Tensor products of module sheaves

For two `𝒪_X`-modules `F` and `G`, construct `F ⊗[𝒪_X] G` by sheafifying
the presheaf `U ↦ F(U) ⊗[𝒪_X(U)] G(U)`.  Prove its balanced universal
property and the canonical stalk isomorphism
`(F ⊗ G)_x ≅ F_x ⊗[𝒪_{X,x}] G_x`.

Pinned Mathlib has the pointwise tensor product of presheaves of modules but
does not expose the resulting tensor product in `X.Modules`; this leaf supplies
that missing sheaf-level interface.

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)
- [The associated sheaf](../sheaves/associated-sheaf.md)

## Proof depends on

- [Sheafification preserves stalks](../sheaves/associated-sheaf-stalks.md)
- Tensor products commute with filtered colimits of modules.

## Sources

- [Hartshorne II.5, tensor product definition on printed p. 109](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
