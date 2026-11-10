---
article_id: af_9792e3a0be9c839d50f33903
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/Affine.lean
---

# A finite principal-open affine criterion

If $f_{1},\ldots ,f_{r} \in \Gamma (X,\mathcal{O} _X)$ generate the unit ideal
and every principal open $X_{f_{i}}$ is affine, then $X$ is affine.

This is Hartshorne's Exercise II.2.17(b). Glue the chart maps to
$\operatorname{Spec}\Gamma(X,\mathcal{O}_X)$ and use the fact that
being an isomorphism is local on the target, as in part (a).

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- [Morphisms to an affine scheme](morphisms-to-affine.md)
- [The qcqs principal-open lemma](qcqs-principal-open-sections.md)

## Sources

- [Hartshorne II.2, Exercise 2.17(a),(b), used in Serre's affineness criterion](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
