---
article_id: af_5e43640b622d3636a61b759b
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ValuationCenter Hartshorne.ValuationCenter.point Hartshorne.exists_valuationCenter_point_eq_iff Hartshorne.functionFieldBaseHom Hartshorne.ValuationCenter.lift_comp_over
---

# Centers of valuations

Let $X$ be an integral scheme over a field $k$, let $K = K(X)$, and let
$R \subseteq K$ be a valuation subring containing $k$. Define a center of $R$ on $X$
to be a lift $\operatorname{Spec} R \longrightarrow X$ of the canonical generic-point morphism
$\operatorname{Spec} K \longrightarrow X$; its underlying point is the image of the closed point of
$\operatorname{Spec} R$.

A point $x\in X$ is the center exactly when the image of
$\mathcal{O}_{X,x}$ in $K(X)$ is dominated by $R$.

Neither the definition nor this characterization uses $k$; when $R$ contains
$k$, every center is a morphism over $\operatorname{Spec} k$, where
$\operatorname{Spec} R$ lies over $\operatorname{Spec} k$ through
$k \subseteq R$, so it is a lift in the valuative square of
$X \longrightarrow \operatorname{Spec} k$.

## Depends on

- [Schemes over a base](../spectrum-and-schemes/over-base.md)
- [Affine opens have fraction field $K(X)$](../normalization-and-exercises/function-field-integral-scheme.md)

## Proof depends on

- [Maps from spectra of valuation rings](valuation-spectrum-map-classification.md)
- The generic point and canonical map from the spectrum of its residue field.
- Domination is local-subring inclusion together with contraction of the maximal ideal.

## Sources

- [Hartshorne II.4, Exercise 4.5](../../../sources/hartshorne-ii-4.md#adopted-exercises)
