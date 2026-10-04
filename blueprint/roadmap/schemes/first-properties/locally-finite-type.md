---
article_id: af_1a29a305023b847c4951dee1
declaration: class
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Morphisms locally of finite type

A morphism `f : X → Y` is locally of finite type when an affine cover of `Y` pulls back to affine covers `Spec Aᵢⱼ` for which each `Aᵢⱼ` is a finitely generated algebra over the corresponding target ring.

Represent the property by Mathlib's every-affine-pair class `LocallyOfFiniteType`. Prove once that target-locality converts Hartshorne's existential cover into this API.

## Depends on

- [Schemes over a base](../spectrum-and-schemes/over-base.md)
- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- Finite type of ring homomorphisms is local under principal localization.

## Sources

- [Hartshorne II.3 (finite-type-and-finite-morphisms)](../../../sources/hartshorne-ii-3.md#finite-type-and-finite-morphisms)

