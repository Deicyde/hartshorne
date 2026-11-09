---
article_id: af_20b90b5104320442f4732041
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.sheafCohomologyIsoExt Hartshorne.sheafCohomologyIsoExt_zero Hartshorne.sheafCohomologyIsoExt_δ
---

# Sheaf cohomology as Ext from the constant sheaf

Let $X$ be a topological space, let $\mathfrak{Ab}(X)$ be the abelian
category of abelian sheaves on $X$ (with groups of sections in the universe
of the underlying set of $X$), and let $\mathbb{Z}_X$ be the constant sheaf
with value $\mathbb{Z}$. Write $\operatorname{Ext}^{n}(\mathbb{Z}_X,F)$ for
the Ext groups of $\mathfrak{Ab}(X)$; they lie in the same universe. For every
$n\ge 0$ there is an isomorphism

$H^{n}(X,F)\cong\operatorname{Ext}^{n}(\mathbb{Z}_X,F)$,

natural in the abelian sheaf $F$, such that:

1. in degree zero it is the composite
   $H^{0}(X,F)\cong\Gamma(X,F)\cong\operatorname{Hom}(\mathbb{Z}_X,F)=\operatorname{Ext}^{0}(\mathbb{Z}_X,F)$
   of the degree-zero identification of cohomology with global sections, the
   inverse of the map sending a morphism $\mathbb{Z}_X\to F$ to the image of
   the global section $1$, and the identification of degree-zero Ext with Hom;
2. for every short exact sequence
   $0\longrightarrow F'\longrightarrow F\longrightarrow F''\longrightarrow 0$
   of abelian sheaves and every $n\ge 0$, it carries the connecting
   homomorphism $H^{n}(X,F'')\longrightarrow H^{n+1}(X,F')$ to the connecting
   homomorphism
   $\operatorname{Ext}^{n}(\mathbb{Z}_X,F'')\longrightarrow\operatorname{Ext}^{n+1}(\mathbb{Z}_X,F')$,
   the Yoneda product with the class of the sequence in
   $\operatorname{Ext}^{1}(F'',F')$.

Thus the two families of functors are isomorphic as delta functors, by an
isomorphism extending the canonical one in degree zero.

Both sides are computed from an injective resolution $F\to I^{\bullet}$:
$H^{n}(X,F)$ is the cohomology of $\Gamma(X,I^{\bullet})$, and
$\operatorname{Ext}^{n}(\mathbb{Z}_X,F)$ is the cohomology of
$\operatorname{Hom}(\mathbb{Z}_X,I^{\bullet})$. The natural isomorphism
$\operatorname{Hom}(\mathbb{Z}_X,-)\cong\Gamma(X,-)$, applied termwise,
identifies the two complexes; compatibility with connecting homomorphisms is
checked on the horseshoe resolution of a short exact sequence. This
comparison is a project bridge between Hartshorne's definition and the Ext
description of cohomology.

## Depends on

- [Sheaf cohomology](../../sheaf-cohomology/sheaf-cohomology.md)
- [The long exact sequence of right derived functors](../../derived-functors/right-derived-long-exact-sequence.md)
- [Global Ext groups](global-ext-groups.md)
- [The covariant long exact sequence of global Ext](global-ext-covariant-long-exact.md)
- [The constant sheaf](../../../schemes/sheaves/constant-sheaf.md)

## Proof depends on

- [Abelian sheaves have enough injectives](../../sheaf-cohomology/abelian-sheaves-enough-injectives.md)
- [Global Ext from an injective resolution](global-ext-injective-resolution.md)

## Sources

- [Hartshorne III.2, definition of sheaf cohomology, printed p. 207](../../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)
- [Hartshorne III.6, Proposition 6.3(c), printed p. 234, for the ringed space with structure sheaf the constant sheaf](../../../../sources/hartshorne-iii-6.md#definitions-and-restriction-printed-pp233234)
