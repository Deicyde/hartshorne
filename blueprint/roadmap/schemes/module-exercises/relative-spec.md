---
article_id: af_2eb3f3aa1e9994fae1979d0f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.relativeSpecEquiv Hartshorne.QuasiCoherentAlgebra Hartshorne.QuasiCoherentAlgebra.relSpec Hartshorne.QuasiCoherentAlgebra.relSpecToBase Hartshorne.QuasiCoherentAlgebra.isAffineHom_relSpecToBase Hartshorne.QuasiCoherentAlgebra.restrictIso Hartshorne.QuasiCoherentAlgebra.restrictIso_hom_fromSpec Hartshorne.QuasiCoherentAlgebra.isPullback_ι Hartshorne.QuasiCoherentAlgebra.pushforwardStructureSheafIso Hartshorne.QuasiCoherentAlgebra.ofHom Hartshorne.QuasiCoherentAlgebra.relSpecOfHomIso Hartshorne.QuasiCoherentAlgebra.relSpecOfHomIso_hom_comp Hartshorne.relativeSpecEquiv_mk Hartshorne.relativeSpecEquiv_symm_mk
---

# Relative Spec of a quasi-coherent algebra

For a quasi-coherent sheaf $A$ of $\mathcal{O}_Y$-algebras, construct an affine morphism

$\operatorname{Spec} _Y A \to Y$

whose inverse image over every affine $V \subseteq Y$ is $\operatorname{Spec} A(V)$, with
$f_*\mathcal{O}_{\operatorname{Spec} _Y A} \cong A$. Conversely, every affine morphism is canonically of
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
