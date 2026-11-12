---
article_id: af_0754912666b82a9d3d2e387d
declaration: isomorphism
origin: cited
lean: AlgebraicGeometry.sectionsPresheaf AlgebraicGeometry.isSheaf_sectionsPresheaf AlgebraicGeometry.GeometricVectorBundle.coordY AlgebraicGeometry.GeometricVectorBundle.sectionsModule AlgebraicGeometry.GeometricVectorBundle.sectionsModuleForgetIso AlgebraicGeometry.GeometricVectorBundle.coordY_add AlgebraicGeometry.GeometricVectorBundle.coordY_smul AlgebraicGeometry.GeometricVectorBundle.sectionsModule_isLocallyFreeOfRank AlgebraicGeometry.Scheme.Modules.vectorBundleSectionsIso AlgebraicGeometry.Scheme.Modules.vectorBundleSectionsIso_hom_eval AlgebraicGeometry.Scheme.Modules.vectorBundleSectionsModuleIso
statement: formalized
proof: formalized
---

# Sections of a geometric vector bundle

The sections of a geometric vector bundle $V \to Y$ form a locally free
$\mathcal{O}_Y$-module of the same rank. For Hartshorne's bundle
$V(E)=\operatorname{Spec} _Y \operatorname{Sym} (E)$, there is a natural isomorphism

$\operatorname{Sections}(V(E)/Y)\cong E^\vee$.

This dual is essential: an algebra map $\operatorname{Sym} (E) \to \mathcal{O}_Y$ is determined by an
$\mathcal{O}_Y$-linear map $E \to \mathcal{O}_Y$.

## Depends on

- [Geometric vector bundles from locally free sheaves](geometric-vector-bundle.md)
- [Finite locally free duality](../modules-and-quasicoherent/finite-locally-free-duality.md)

## Sources

- [Hartshorne II.5, Exercise 5.18(b,c) (p.129)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
