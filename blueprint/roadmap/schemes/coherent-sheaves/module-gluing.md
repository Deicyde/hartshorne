---
article_id: af_cc5b776dbee778ca137f2f01
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.ModuleGluing.GluingData.exists_unique_gluing Hartshorne.ModuleGluing.GluingData Hartshorne.ModuleGluing.SchemeGluingData.exists_unique_gluing Hartshorne.ModuleGluing.SchemeGluingData
---

# Gluing sheaves of modules along open immersions

Let $(X,\mathcal{O}_X)$ be a ringed space and let $\{U_i\}$ be an open cover of $X$, that is,
a family of open immersions $U_i \hookrightarrow X$ whose images cover $X$. Write
$U_{ij} = U_i \cap U_j$ and $U_{ijk} = U_i \cap U_j \cap U_k$. Suppose given, for each $i$, an
$\mathcal{O}_X|_{U_i}$-module $\mathcal{F}_i$, and for each $i,j$ an isomorphism of
$\mathcal{O}_X|_{U_{ij}}$-modules

$\varphi_{ij} : \mathcal{F}_i|_{U_{ij}} \to \mathcal{F}_j|_{U_{ij}}$

such that

1. $\varphi_{ii} = \mathrm{id}$ for each $i$, and
2. $\varphi_{ik} = \varphi_{jk} \circ \varphi_{ij}$ on $U_{ijk}$ for each $i,j,k$.

Then there is an $\mathcal{O}_X$-module $\mathcal{F}$ together with isomorphisms of
$\mathcal{O}_X|_{U_i}$-modules $\psi_i : \mathcal{F}|_{U_i} \to \mathcal{F}_i$ such that
$\psi_j = \varphi_{ij} \circ \psi_i$ on $U_{ij}$ for all $i,j$. It is unique up to unique
isomorphism: if $(\mathcal{F}', \psi'_i)$ is another such family, there is exactly one
isomorphism of $\mathcal{O}_X$-modules $\alpha : \mathcal{F} \to \mathcal{F}'$ with
$\psi'_i \circ \alpha|_{U_i} = \psi_i$ for every $i$.

This is the gluing of sheaves on an open cover, with $\mathcal{O}_X$-module structures carried
along. Glue the underlying sheaves of abelian groups. Over an open $V$, a section of the glued
sheaf is a family of sections $s_i \in \mathcal{F}_i(V \cap U_i)$ with
$\varphi_{ij}(s_i) = s_j$ on $V \cap U_{ij}$. Because each $\varphi_{ij}$ is
$\mathcal{O}$-linear, multiplying every $s_i$ by the restriction of one $a \in \mathcal{O}_X(V)$
preserves this condition. The uniqueness isomorphism is $\mathcal{O}_X$-linear because it is
linear on each $U_i$.

## Depends on

- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)

## Informally uses

- [Gluing sheaves on an open cover](../sheaf-functors/gluing-sheaves.md)

## Sources

- [Hartshorne II.1, Exercise 1.22 (p. 69), glues sheaves; the module form here is a project bridge](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
- [Hartshorne II.7, relative Proj construction (p. 160), where the twisting sheaves of the affine pieces are glued](../../../sources/hartshorne-ii-7.md#relative-proj-and-projective-bundles)
