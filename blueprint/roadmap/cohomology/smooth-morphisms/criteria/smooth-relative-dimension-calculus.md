---
article_id: af_96e5110c49ccdf5d1fd45eac
declaration: theorem
origin: cited
source_units: [chapter-iii-section-10]
statement: formalized
proof: formalized
lean: Hartshorne.openImmersion_smoothOfRelativeDimension_zero Hartshorne.smoothOfRelativeDimension_baseChange Hartshorne.smoothOfRelativeDimension_comp Hartshorne.smoothOfRelativeDimension_product
---

# Smooth relative-dimension calculus

Open immersions are smooth of relative dimension zero. Smoothness of relative
dimension `n` is preserved by arbitrary base change. If `f` and `g` are smooth
of relative dimensions `n` and `m`, their composite is smooth of relative
dimension `n+m`; consequently the product over a common base has relative
dimension `n+m`.

This source proposition is a wrapper around several pinned morphism-property
declarations and is not itself an exact upstream theorem.

## Depends on

- [Schemes have fibre products](../../../schemes/fiber-products/schemes-have-fiber-products.md)

## Proof depends on

- `AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange` and
  `AlgebraicGeometry.smoothOfRelativeDimension_comp` in pinned Mathlib.

## Sources

- [Hartshorne III.10, Proposition 10.1, pp.268–269](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
