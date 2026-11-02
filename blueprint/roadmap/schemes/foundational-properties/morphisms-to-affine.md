---
article_id: af_28fa997940eb0b698a2291fd
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.ΓSpec.adjunction
mathlib_file: Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean
---

# Morphisms to an affine scheme

For a scheme $X$ and a commutative ring $A$, there is a natural equivalence

$\operatorname{Hom}_{\mathrm{Sch}}(X,\operatorname{Spec}A)\cong\operatorname{Hom}_{\mathrm{CRing}}(A,\Gamma(X,\mathcal{O}_X))$.

This is Hartshorne's Exercise II.2.4, the global-sections–spectrum
adjunction. Its unit is $X\to\operatorname{Spec}\Gamma(X,\mathcal{O}_X)$,
and its counit is the global-sections isomorphism for an affine spectrum.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- [Spec is fully faithful](../spectrum-and-schemes/spec-fully-faithful.md)

## Sources

- [Hartshorne II.2, Exercise 2.4, used in products and later constructions (p. 79)](../../../sources/hartshorne-ii-2.md#exercises-21-through-29)
