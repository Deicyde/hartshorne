---
article_id: af_4ca05bb2cb060de6a13e3554
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-abstract-curves]
---

# Nonsingular affine curves have Dedekind coordinate rings

Let `Y` be a nonsingular affine curve.  Its coordinate ring `A(Y)` is a
Dedekind domain of Krull dimension one.

The coordinate ring is a Noetherian domain and has dimension one because `Y`
is an affine curve.  For every maximal ideal `𝔪_P`, Theorem 3.2(c)
identifies `A(Y)_{𝔪_P}` with the local ring at `P`; that local ring is a
DVR by nonsingularity.  Integral closedness is local at maximal ideals, so
`A(Y)` is integrally closed.

This is the converse direction to the affine-model construction.  It is kept
separate because the openness proof in Proposition 6.7 starts with an
arbitrary affine open subset of the given curve, not with a normalization
model constructed earlier.

## Depends on

- [Curves](../nonsingular-curves/curve.md)
- [Intrinsic nonsingularity](../nonsingular-varieties/intrinsic-nonsingularity.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Points and maximal ideals](../morphisms/points-eq-maximal-ideals.md)
- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)
- [Local rings of nonsingular curves are DVRs](../nonsingular-curves/nonsingular-curve-local-ring-dvr.md)

## Sources

- [Hartshorne I.6, proof of Proposition 6.7 (pp. 42--43)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
