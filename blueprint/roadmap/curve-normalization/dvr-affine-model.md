---
article_id: af_99c0d90cb858f171e4e80de6
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-normalization]
---

# Every function-field DVR has a nonsingular affine model

Let `k` be algebraically closed, let `K/k` be an essentially finite-type field
extension with `Algebra.trdeg k K = 1`, and let `R ∈ C_K`. There are a
nonsingular affine curve `Y` with affine-variety witness `hY`, a point `P ∈ Y`,
and compatible `k`-algebra equivalences

`e_K : Hartshorne.FunctionField hY.isIrreducible ≃ₐ[k] K` and
`e_R : Hartshorne.LocalRingAt hY.isIrreducible P ≃ₐ[k]
  R.toValuationSubring`.

This is Corollary 6.6. Choose a separating parameter `t`. The valuation-ring
property says that `R` contains `t` or `t⁻¹`; use the corresponding one of
the two finite Dedekind normalization charts. Its center at `R` is a maximal
ideal, and the localization at that center is `R`. The affine-model theorem
turns precisely this localization into the local ring of a point on a
nonsingular affine curve.

Retain compatibility with the embeddings into `K`, not merely an abstract
ring equivalence. Require the pointwise equation

`e_K (localToFunctionField hY.isIrreducible P z) = (e_R z : K)`

for every `z : Hartshorne.LocalRingAt hY.isIrreducible P`. Proposition 6.7
uses this compatibility to identify residue maps and points of the valuation
space. This commuting square strengthens Corollary 6.6's stated abstract
isomorphism for downstream use; it does not change the source-facing
conclusion.

## Depends on

- [Discrete valuation rings of a function field](function-field-dvrs.md)
- [Curves](../nonsingular-curves/curve.md)
- [Intrinsic nonsingularity](../nonsingular-varieties/intrinsic-nonsingularity.md)

## Proof depends on

- [The two separable normalization charts](separable-normalization-charts.md)
- [A DVR containing a Dedekind subring is its localization](dedekind-subring-localization.md)
- [Dedekind localizations occur on nonsingular affine curves](dedekind-affine-model.md)

## Sources

- [Hartshorne I.6, Corollary 6.6 (p. 42)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
