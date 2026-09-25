---
article_id: af_64778191cf786477556c0eb8
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-normalization]
statement: formalized
proof: formalized
lean: Hartshorne.exists_dedekind_affine_model
---

# Dedekind localizations occur on nonsingular affine curves

Let `k` be algebraically closed. Let `B` be a finitely generated `k`-algebra
domain which is Dedekind of exact Krull dimension one, and let `K` be a chosen
fraction field with compatible instances
`[Algebra B K] [IsFractionRing B K] [Algebra k K]
[IsScalarTower k B K]`. For a maximal ideal `℘` of `B`, there are an affine
variety `Y` with witness `hY`, a point `P ∈ Y`, and compatible `k`-algebra
equivalences

`e_B : A(Y) ≃ₐ[k] B`,
`e_K : Hartshorne.FunctionField hY.isIrreducible ≃ₐ[k] K`, and
`e_P : Hartshorne.LocalRingAt hY.isIrreducible P ≃ₐ[k] B_℘`

such that `Y` is a nonsingular curve and

`Ideal.map e_B.toRingEquiv (𝔪_P) = ℘`.

Write `ι_℘ : B_℘ →ₐ[k] K` for the canonical localization map. Compatibility
means that both equations

`e_K (coordToRational hY.isIrreducible a) = algebraMap B K (e_B a)`

and

`e_K (localToFunctionField hY.isIrreducible P z) = ι_℘ (e_P z)`

hold for every `a : A(Y)` and
`z : Hartshorne.LocalRingAt hY.isIrreducible P`. State these commuting
squares explicitly rather than retaining three unrelated abstract
equivalences. Use this affine presentation consistently; do not mix it with
the separate bundled `Variety.FunctionField` API.

Realize `B` as a coordinate ring using Remark 1.4.6 and transport `℘` to a
point by Theorem 3.2(b).  Dimension of the coordinate ring makes `Y` a curve.
At every point, Theorem 3.2(c) identifies the local ring with a localization
of `B`; that localization is a DVR, hence regular local, so `Y` is
nonsingular.

The chosen-fraction-field and local-ring compatibility is needed both for the
valuation-space infinitude argument and for residue-field transport.

## Depends on

- [Curves](../nonsingular-curves/curve.md)
- [Intrinsic nonsingularity](../nonsingular-varieties/intrinsic-nonsingularity.md)

## Proof depends on

- [Every finitely generated domain is a coordinate ring](../affine-varieties/coordinate-ring-realization.md)
- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Points and maximal ideals](../morphisms/points-eq-maximal-ideals.md)
- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)
- [The function field is the fraction field](../morphisms/function-field-is-fraction-field.md)
- [Localizations of a Dedekind domain are DVRs](../nonsingular-curves/dedekind-localization-dvr.md)
- [Characterizations of discrete valuation rings](../nonsingular-curves/dvr-characterizations.md)
- [The function field is the fraction field of every local ring](../nonsingular-curves/local-ring-fraction-field.md)

## Sources

- [Hartshorne I.6, affine curve constructed in Lemma 6.5 and Corollary 6.6 (pp. 41--42)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
