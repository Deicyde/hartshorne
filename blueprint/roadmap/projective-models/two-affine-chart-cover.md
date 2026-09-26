---
article_id: af_7157364b8a6b0f58790df1e7
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
---

# A two-chart affine cover of the valuation curve

For a one-dimensional function field `K/k`, the two fixed separable
normalization charts determine nonsingular affine curves `U₀` and `U₁`,
compatible embeddings of their function fields into `K`, and open embeddings
of `U₀` and `U₁` into `C_K` whose images cover `C_K`.  The sole main
declaration is planned as
`Hartshorne.ValuationSpace.exists_two_affine_model_cover`.

This is the finite affine cover selected in the first paragraph of the proof
of Theorem 6.9.  Specializing Hartshorne's quasi-compactness argument to the
already-formalized `k[t]` and `k[t⁻¹]` models avoids a new heterogeneous
finite-product API without imposing separability on `K/k`.

## Depends on

- [The two separable normalization charts](../curve-normalization/separable-normalization-charts.md)
- [Every function-field DVR has a nonsingular affine model](../curve-normalization/dvr-affine-model.md)
- [Abstract nonsingular curves](../curve-normalization/abstract-nonsingular-curve.md)

## Proof depends on

- [Transporting valuation curves along a field equivalence](valuation-space-field-equivalence.md)
- [Nonsingular curves are open subcurves of their valuation spaces](../curve-normalization/curve-to-valuation-space-iso.md)

## Sources

- [Hartshorne I.6, first paragraph of the proof of Theorem 6.9 (p. 44)](../../sources/hartshorne.md#i6-projective-models)
