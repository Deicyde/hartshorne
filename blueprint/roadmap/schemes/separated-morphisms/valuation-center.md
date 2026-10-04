---
article_id: af_5e43640b622d3636a61b759b
declaration: def
origin: cited
source_units: [chapter-ii-section-4]
---

# Centers of valuations

Let `X` be an integral scheme over a field `k`, let `K = K(X)`, and let
`R ⊆ K` be a valuation subring containing `k`. Define a center of `R` on `X`
to be a lift `Spec R ⟶ X` of the canonical generic-point morphism
`Spec K ⟶ X`; its underlying point is the image of the closed point of
`Spec R`.

Prove as supporting API that `x : X` is this underlying center exactly when the
image of `𝒪_{X,x}` in `K(X)` is dominated by `R`. The lift-based definition
is canonical in Mathlib and postpones all chosen stalk-to-function-field
embeddings to this equivalence theorem.

## Depends on

- [Schemes over a base](../spectrum-and-schemes/over-base.md)
- [Affine opens have fraction field `K(X)`](../normalization-and-exercises/function-field-integral-scheme.md)

## Proof depends on

- [Maps from spectra of valuation rings](valuation-spectrum-map-classification.md)
- The generic point and canonical map from the spectrum of its residue field.
- `LocalSubring.le_def`, identifying its order with domination.

## Sources

- [Hartshorne II.4, Exercise 4.5](../../../sources/hartshorne-ii-4.md#adopted-exercises)
