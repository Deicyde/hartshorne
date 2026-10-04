---
article_id: af_4e17f763aa8b789939a367cb
declaration: def
origin: cited
source_units: [chapter-ii-section-8, chapter-i-section-8-decomposed-previews]
---

# The relative differential sheaf

For a scheme morphism `f : X → Y`, construct an `𝒪_X`-module `Ω[X/Y]` and a
map of sheaves of abelian groups `d : 𝒪_X → Ω[X/Y]` satisfying the Leibniz
rule, universal among derivations that vanish on the image of
`f⁻¹𝒪_Y → 𝒪_X`.  The derivation is not an `𝒪_X`-linear morphism.

Use an affine-local construction and glue it, or construct the universal
sheaf directly.  Prove the canonical comparison with the conormal sheaf of
the diagonal `Δ : X → X ×_Y X`.  For a general morphism the diagonal is an
immersion rather than necessarily a closed immersion, so this comparison must
also prove independence of the open neighborhood in which `Δ` is closed.

## Depends on

- [Schemes over a base](../../spectrum-and-schemes/over-base.md)
- [Sheaves of modules](../../modules-and-quasicoherent/sheaves-of-modules.md)
- [Pushforward, pullback, and their adjunction](../../modules-and-quasicoherent/module-push-pull-adjunction.md)
- [The universal module of Kähler differentials](../kaehler-differentials/kahler-differential-universal.md)

## Proof depends on

- Gluing sheaves of modules and their morphisms over an affine-open basis.
- The pinned presheaf-differentials API, whose general-morphism construction
  is currently marked TODO, is only partial prior art.
- Stacks Project, Lemma 29.33.7, tag `08S2`, for the general diagonal
  conormal comparison and its independence of auxiliary choices.

## Sources

- [Hartshorne II.8, definition and Remarks 8.9.1–8.9.2, printed p. 175](../../../../sources/hartshorne-ii-8.md)
