---
article_id: af_2eb3f3aa1e9994fae1979d0f
declaration: theorem
origin: cited
statement: retracted
lean: Hartshorne.relativeSpecEquiv Hartshorne.QuasiCoherentAlgebra Hartshorne.QuasiCoherentAlgebra.relSpec Hartshorne.QuasiCoherentAlgebra.relSpecToBase Hartshorne.QuasiCoherentAlgebra.isAffineHom_relSpecToBase Hartshorne.QuasiCoherentAlgebra.restrictIso Hartshorne.QuasiCoherentAlgebra.restrictIso_hom_fromSpec Hartshorne.QuasiCoherentAlgebra.isPullback_ι Hartshorne.QuasiCoherentAlgebra.pushforwardStructureSheafIso Hartshorne.QuasiCoherentAlgebra.ofHom Hartshorne.QuasiCoherentAlgebra.relSpecOfHomIso Hartshorne.QuasiCoherentAlgebra.relSpecOfHomIso_hom_comp Hartshorne.relativeSpecEquiv_mk Hartshorne.relativeSpecEquiv_symm_mk Hartshorne.QuasiCoherentAlgebra.map_ι Hartshorne.QuasiCoherentAlgebra.restriction Hartshorne.QuasiCoherentAlgebra.SpecMap_restriction_ι Hartshorne.QuasiCoherentAlgebra.restriction_map Hartshorne.QuasiCoherentAlgebra.eq_restriction Hartshorne.QuasiCoherentAlgebra.restriction_eq_map Hartshorne.QuasiCoherentAlgebra.restrictIso_inv_homOfLE_restrictIso_hom Hartshorne.QuasiCoherentAlgebra.existsUnique_iso_of_ι
---

# Relative Spec of a quasi-coherent algebra

Let $A$ be a quasi-coherent sheaf of $\mathcal{O}_Y$-algebras. There is a unique scheme $X$
and morphism $f : X \to Y$ such that for every open affine $V \subseteq Y$,
$f^{-1}(V) \cong \operatorname{Spec} A(V)$ as schemes over $V$, and for every inclusion $U \hookrightarrow V$ of open
affines of $Y$, the morphism $f^{-1}(U) \to f^{-1}(V)$ corresponds to the restriction
homomorphism $A(V) \to A(U)$. Here uniqueness means up to a unique isomorphism over $Y$
compatible with these identifications. Write $\operatorname{Spec}_Y A$ for this scheme; the
morphism $f$ is affine, and
$f_*\mathcal{O}_{\operatorname{Spec}_Y A} \cong A$. Conversely, every affine morphism is canonically of
this form. These constructions induce mutually inverse bijections between
isomorphism classes of quasi-coherent $\mathcal{O}_Y$-algebras and isomorphism classes
of affine schemes over $Y$. No categorical equivalence is asserted here.

## Depends on

- [The affine-morphism criterion](affine-morphism-criterion.md)
- [Quasi-coherent affine-local criterion](../modules-and-quasicoherent/quasicoherent-affine-local-criterion.md)

## Proof depends on

- [Gluing schemes](../spectrum-and-schemes/gluing.md)
- [Affine change of rings](../modules-and-quasicoherent/affine-tilde/tilde-affine-change-of-rings.md)

## Sources

- [Hartshorne II.5, Exercise 5.17(c,d) (p.128)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
