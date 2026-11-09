---
article_id: af_a3a60a624675778f44a80899
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.sheafCohomology Hartshorne.sheafCohomologyZeroIso
---

# Sheaf cohomology

Let $X$ be a topological space and let $\mathfrak{Ab}(X)$ be the abelian
category of sheaves of abelian groups on $X$, where the groups of sections
lie in the same universe as the underlying set of $X$. Since
$\mathfrak{Ab}(X)$ has enough injectives and the global section functor
$\Gamma(X,-)\colon \mathfrak{Ab}(X)\longrightarrow\mathfrak{Ab}$ is additive
and left exact, define for every $n\ge 0$ the cohomology functor

$H^{n}(X,-)=R^{n}\Gamma(X,-)\colon \mathfrak{Ab}(X)\longrightarrow\mathfrak{Ab}$

as the $n$-th right derived functor of $\Gamma(X,-)$, computed from
injective resolutions in $\mathfrak{Ab}(X)$. For an abelian sheaf $F$, the
group $H^{n}(X,F)$ is the $n$-th cohomology group of $F$; it lies in the same
universe as the groups of sections. In degree zero there is an isomorphism
$H^{0}(X,F)\cong\Gamma(X,F)$, natural in $F$.

This is Hartshorne's definition. Its identification with the Ext groups
$\operatorname{Ext}^{n}(\mathbb{Z}_X,F)$ out of the constant sheaf is the
separate [comparison with Ext](../ext-groups/global-ext/sheaf-cohomology-ext-comparison.md).

## Depends on

- [Abelian sheaves have enough injectives](abelian-sheaves-enough-injectives.md)
- [Right derived functors](../derived-functors/right-derived-functors.md)
- [Global sections are left exact](../../schemes/sheaf-functors/global-sections-left-exact.md)

## Sources

- [Hartshorne III.2, definition of sheaf cohomology, printed p. 207](../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)
