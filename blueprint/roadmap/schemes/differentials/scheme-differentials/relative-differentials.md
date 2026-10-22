---
article_id: af_4e17f763aa8b789939a367cb
declaration: def
origin: cited
source_units: [chapter-ii-section-8, chapter-i-section-8-decomposed-previews]
lean: AlgebraicGeometry.Scheme.relativeDifferentialsWithDerivation
statement: formalized
proof: formalized
---

# The relative differential sheaf

For a scheme morphism `f : X → Y`, construct an `𝒪_X`-module `Ω[X/Y]` and a
map of sheaves of abelian groups `d : 𝒪_X → Ω[X/Y]` satisfying the Leibniz
rule and vanishing on the image of `f⁻¹𝒪_Y → 𝒪_X`. The derivation is not an
`𝒪_X`-linear morphism.

Construct the sheaf directly from the presheaf of relative differentials and
sheafification. Its universal property and the comparison with Hartshorne's
conormal-sheaf definition are recorded separately, so this definition does not
presuppose a theory of conormal sheaves for arbitrary immersions.

## Depends on

- [Schemes over a base](../../spectrum-and-schemes/over-base.md)
- [Sheaves of modules](../../modules-and-quasicoherent/sheaves-of-modules.md)
- [Pushforward, pullback, and their adjunction](../../modules-and-quasicoherent/module-push-pull-adjunction.md)
- [The universal module of Kähler differentials](../kaehler-differentials/kahler-differential-universal.md)

## Proof depends on

- The pinned `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`
  construction followed by sheafification.

## Sources

- [Hartshorne II.8, definition and Remarks 8.9.1–8.9.2, printed p. 175](../../../../sources/hartshorne-ii-8.md)
