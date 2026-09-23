---
article_id: af_64778191cf786477556c0eb8
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-normalization]
---

# Dedekind localizations occur on nonsingular affine curves

Let `B` be a finitely generated `k`-algebra domain which is Dedekind of exact
Krull dimension one, and let `℘` be a maximal ideal of `B`.  There are an
affine variety `Y`, a point `P ∈ Y`, and a `k`-algebra equivalence
`A(Y) ≃ B` carrying `𝔪_P` to `℘`, such that `Y` is a nonsingular curve and

`B_℘ ≃ 𝒪_{P,Y}`.

Realize `B` as a coordinate ring using Remark 1.4.6 and transport `℘` to a
point by Theorem 3.2(b).  Dimension of the coordinate ring makes `Y` a curve.
At every point, Theorem 3.2(c) identifies the local ring with a localization
of `B`; that localization is a DVR, hence regular local, so `Y` is
nonsingular.

The theorem should also expose the induced equivalence between `K(Y)` and any
chosen fraction field of `B`.  This compatibility is needed both for the
valuation-space infinitude argument and for residue-field transport.

## Depends on

- [Curves](../nonsingular-curves/curve.md)
- [Intrinsic nonsingularity](../nonsingular-varieties/intrinsic-nonsingularity.md)

## Proof depends on

- [Every finitely generated domain is a coordinate ring](../affine-varieties/coordinate-ring-realization.md)
- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Points and maximal ideals](../morphisms/points-eq-maximal-ideals.md)
- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)
- [Localizations of a Dedekind domain are DVRs](../nonsingular-curves/dedekind-localization-dvr.md)
- [Characterizations of discrete valuation rings](../nonsingular-curves/dvr-characterizations.md)

## Sources

- [Hartshorne I.6, affine curve constructed in Lemma 6.5 and Corollary 6.6 (pp. 41--42)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
