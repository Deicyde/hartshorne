---
article_id: af_238f8cf474ceb885acdb0312
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.GradedGlobalSections.gammaStarModule Hartshorne.GradedGlobalSections.GammaStar Hartshorne.GradedGlobalSections.smul_of Hartshorne.GradedGlobalSections.twistSection Hartshorne.GradedGlobalSections.mulMap Hartshorne.GradedGlobalSections.mulMap_mul Hartshorne.GradedGlobalSections.mulMap_one Hartshorne.GradedGlobalSections.twistMulHom_tmul_twistSection_apply
---

# The graded global-sections module

For $X = \operatorname{Proj} S$ and a sheaf $F$ of $\mathcal{O}_X$-modules, define

$\Gamma_*(F)=\bigoplus_{n\in\mathbb{Z}}\Gamma(X,F(n))$

as a graded $S$-module. Multiplication by a homogeneous $s \in S_d$ is induced
by the section of $\mathcal{O}_X(d)$ determined by $s$ and the twist-tensor
isomorphism.

## Depends on

- [Twists and graded shifts](proj-twist-compatibility.md)
- [Sections of a sheaf of modules](../modules-and-quasicoherent/sheaves-of-modules.md)

## Sources

- [Hartshorne II.5, definition of the associated graded module (p.118)](../../../sources/hartshorne-ii-5.md#graded-modules-twists-and-reconstruction-on-proj)
