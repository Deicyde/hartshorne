---
article_id: af_3232a70a7349c763871b3c37
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.genericCompletionFunctor Hartshorne.genericCompletionAlpha Hartshorne.genericCompletionOpensOrderIso
---

# The generic-completion functor

Define a functor $t$ on topological spaces. For a space $X$, the points of
$t(X)$ are its nonempty irreducible closed subsets. For each closed subset
$Y\subseteq X$, the set

$$t(Y)=\{Z\in t(X)\mid Z\subseteq Y\}$$

is closed in $t(X)$. For a continuous map $f:X\to Y$, send $Z$ to the
closure of $f(Z)$.

The construction respects identity maps and composition. The map
$\alpha_X:X\to t(X)$ given by $x\mapsto\overline{\{x\}}$ induces
an order isomorphism between the open subsets of $X$ and $t(X)$.

## Depends on

- Nothing in this roadmap.

## Sources

- [Hartshorne II.2, construction of $t(X)$ in Proposition 2.6 (p. 78)](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)
