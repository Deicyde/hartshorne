---
article_id: af_f892625ca28500dec147e4d2
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.Ringed.moduleSkyscraper Hartshorne.Ringed.moduleStalkFunctor Hartshorne.Ringed.moduleStalkSkyscraperAdjunction
---

# Skyscraper module sheaves and the stalk adjunction

Let $(X,\mathcal{O}_X)$ be a ringed space, $x \in X$, and $N$ an
$\mathcal{O}_{X,x}$-module. The skyscraper sheaf $i_x(N)$, with
$\Gamma(U, i_x(N)) = N$ when $x \in U$ and $0$ otherwise, and with identity or
zero restriction maps, is a sheaf of $\mathcal{O}_X$-modules: a section
$s \in \mathcal{O}_X(U)$ with $x \in U$ acts on $N$ through its germ $s_x$.
The construction is functorial in $N$, and the stalk functor $F \mapsto F_x$,
from $\mathcal{O}_X$-modules to $\mathcal{O}_{X,x}$-modules, is left adjoint to
it:

$\operatorname{Hom}_{\mathcal{O}_X}(F, i_x(N)) \cong \operatorname{Hom}_{\mathcal{O}_{X,x}}(F_x, N)$,

naturally in $F$ and $N$. A linear map $\varphi : F_x \to N$ corresponds to the
morphism sending a section $t \in F(U)$, for $x \in U$, to $\varphi(t_x)$.

The sheaf axiom for $i_x(N)$ holds because a cover of an open containing $x$
has a member containing $x$. A morphism $F \to i_x(N)$ is compatible with
restriction to smaller neighbourhoods of $x$, so it factors uniquely through
the stalk $F_x$.

## Depends on

- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- The stalk is the colimit of the sections over neighbourhoods of $x$, so a
  compatible family of maps out of those sections factors through it.

## Sources

- [Hartshorne II.1, Exercise 1.17 (skyscraper sheaves), exercises pp.66–69](../../../sources/hartshorne-ii-1.md#excluded-and-deferred-exercises)
