---
article_id: af_8de0051a2ba38409615eb538
declaration: isomorphism
origin: cited
source_units: [chapter-ii-section-5]
statement: formalized
proof: formalized
lean: Hartshorne.affineTildeCoproductNatIso Hartshorne.affineTildeCoproductIso
---

# Tilde commutes with direct sums

For every family of `A`-modules `Mᵢ`, construct the natural isomorphism

`(⨁ i, Mᵢ)̃ ≅ ⨁ i, M̃ᵢ`.

This is Proposition 5.2(c).  It is separated from tensor compatibility because
its proof and completion criterion are purely cocontinuous: tilde, as a left
adjoint, preserves coproducts.

## Depends on

- [The affine tilde sheaf and localization](tilde-localization.md)
- [Sheaves of modules](sheaves-of-modules.md)

## Proof depends on

- [The tilde–global-sections adjunction](tilde-gamma-adjunction.md)
- Left adjoints preserve coproducts.

## Sources

- [Hartshorne II.5, Proposition 5.2(c) on printed p. 111](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
