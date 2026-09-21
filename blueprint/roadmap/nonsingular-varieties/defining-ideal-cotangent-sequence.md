---
article_id: af_0501b46f3624fa99b6ff84e1
declaration: theorem
origin: cited
source_units: [chapter-i-section-5-geometry]
statement: formalized
lean: Hartshorne.definingIdealCotangentEquiv_nonempty Hartshorne.residueField_smul_cotangentSpace_eq_baseField_smul Hartshorne.definingIdealGradient_apply Hartshorne.affineCoordinatesToLocalCotangent_surjective Hartshorne.affineCoordinatesToLocalCotangent_ker Hartshorne.finrank_localCotangent_add_finrank_gradientSpace
---

# The defining ideal and the local cotangent space

Let `Y ⊆ 𝔸ⁿ` be an affine variety, `P ∈ Y`,
`𝔟 = I(Y)`, and `𝔫_P` the maximal ideal of the ambient polynomial ring at
`P`. If `𝔪` is the maximal ideal of `𝒪_{P,Y}`, then the residue-field
identification `𝒪_{P,Y}/𝔪 ≃ k` gives a `k`-linear model

`𝔪/𝔪² ≃ₗ[k] 𝔫_P/(𝔟 + 𝔫_P²)`.

Combining this with the ambient derivative equivalence gives an exact quotient
of `kⁿ` by the span of the gradients `θ_P(𝔟)`. In particular,

`dim_k(𝔪/𝔪²) + dim_k span{∇f(P) | f ∈ I(Y)} = n`.

This is the dimension count in the proof of Theorem 5.1. Formally, it is the
bridge between three representations already present in the libraries: the
project's germ local ring, its localization model
`A(Y)_{𝔪_P}`, and Mathlib's `Ideal.Cotangent`/`IsLocalRing.CotangentSpace`.
The equivalences must also respect the project's residue-field equivalence with
`k`; a bare ring equivalence is not enough to rewrite vector-space dimensions.

Mathlib's closest reusable pieces are
`Algebra.Extension.exact_cotangentComplex_toKaehler`,
`Algebra.Generators.Cotangent.exact`, and `Ideal.tensorCotangentEquiv`.
None directly transports the cotangent space through this project's
localization and germ-ring equivalences, so that scalar-compatible bridge is
the principal implementation risk in this node.

## Depends on

- [The cotangent space of affine space](ambient-cotangent-space.md)
- [The local ring is local](../morphisms/local-ring-is-local.md)
- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)
- [Points and maximal ideals](../morphisms/points-eq-maximal-ideals.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Sources

- [Hartshorne I.5, proof of Theorem 5.1 (p. 32)](../../sources/hartshorne.md#i5)
