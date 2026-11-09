---
article_id: af_b98f93c716bddeea19728e16
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.ArtinReesKernelSheaf.isQuasicoherent_powSmul Hartshorne.ArtinReesKernelSheaf.sub_powSmul_eq Hartshorne.ArtinReesKernelSheaf.isCoherent_powSmul Hartshorne.ArtinReesKernelSheaf.powSmul Hartshorne.ArtinReesKernelSheaf.powSmul_zero
---

# Product of an ideal sheaf with a submodule sheaf

Let $X$ be a scheme, let $\mathcal{I} \subseteq \mathcal{O}_X$ be a quasi-coherent ideal sheaf,
let $N$ be a quasi-coherent $\mathcal{O}_X$-module, and let $k \ge 0$. Define the subsheaf
$\mathcal{I}^k N \subseteq N$ whose sections over an open $U$ are the $s \in N(U)$ such that every
$x \in U$ has an affine open neighbourhood $V \subseteq U$ with $s|_V \in \mathcal{I}(V)^k N(V)$. Then:

1. $\mathcal{I}^k N$ is a quasi-coherent $\mathcal{O}_X$-module;
2. for every affine open $V \subseteq X$,
   $\Gamma(V, \mathcal{I}^k N) = \mathcal{I}(V)^k \, N(V)$ as submodules of $N(V)$; and
3. if $X$ is Noetherian and $N$ is coherent, then $\mathcal{I}^k N$ is coherent.

When $N$ is a quasi-coherent submodule of an $\mathcal{O}_X$-module $E$, the same subsheaf
$\mathcal{I}^k N$ is a submodule of $E$. The case $k = 0$ gives $\mathcal{I}^0 N = N$.

Proof sketch. All three claims are local, so take $V = \operatorname{Spec} A$ affine. Write
$\mathfrak{a} = \mathcal{I}(V)$ and $M = N(V)$, so that $\mathcal{I}|_V \cong \widetilde{\mathfrak{a}}$ and
$N|_V \cong \widetilde{M}$. The submodule $\mathfrak{a}^k M \subseteq M$ gives a quasi-coherent
subsheaf $\widetilde{\mathfrak{a}^k M} \subseteq \widetilde{M}$. On a basic open $D(f)$ its sections
are $(\mathfrak{a}^k M)_f = (\mathfrak{a}_f)^k M_f$, and $\mathfrak{a}_f = \mathcal{I}(D(f))$ and
$M_f = N(D(f))$. Membership in $\mathcal{I}(W)^k N(W)$ is preserved by restriction to smaller
affine opens, so the local condition defining $\mathcal{I}^k N$ may be tested on basic opens of
$V$. A section of $N$ over an open subset of $V$ therefore lies in $\mathcal{I}^k N$ exactly when it
lies locally in the subsheaf $\widetilde{\mathfrak{a}^k M}$, so
$(\mathcal{I}^k N)|_V = \widetilde{\mathfrak{a}^k M}$. This gives (1), and taking global sections over
$V$ gives (2). For (3), $A$ is Noetherian and $M$ is finite, so $\mathfrak{a}^k M$ is finite.

## Depends on

- [Sheaves of modules](../modules-and-quasicoherent/sheaves-of-modules.md)
- [The affine-local criterion for quasi-coherence](../modules-and-quasicoherent/quasicoherent-affine-local-criterion.md)
- [The affine-local criterion for coherence](../modules-and-quasicoherent/coherent-affine-local-criterion.md)

## Proof depends on

- [Modules and quasi-coherent sheaves on an affine scheme](../modules-and-quasicoherent/affine-quasicoherent-equivalence.md)
- [The affine tilde sheaf and localization](../modules-and-quasicoherent/affine-tilde/tilde-localization.md)
- [Exactness of the tilde functor](../modules-and-quasicoherent/affine-tilde/tilde-exactness.md)
- Localization commutes with products of ideals and submodules:
  $(\mathfrak{a}^k M)_f = (\mathfrak{a}_f)^k M_f$.
- Membership in a subsheaf is a local condition, and basic opens form a basis of an affine scheme.
- Over a Noetherian ring, a submodule of a finite module is finite.

## Sources

- [Hartshorne II.9, completion of a coherent sheaf (p.194): the quotients $F/\mathcal{I}^{n+1} F$; the product sheaf and its quasi-coherence are a project bridge](../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
- [Hartshorne II.5, ideal sheaves, Definition and Proposition 5.9 (pp.115–116)](../../../sources/hartshorne-ii-5.md#ideal-sheaves-and-closed-subschemes)
- [Hartshorne III.11, final Artin–Rees step in Theorem 11.1 (p.279), whose kernel systems the roadmap states for sheaves](../../../sources/hartshorne-iii-11-12.md#infinitesimal-fibres-and-formal-functions-pp276279)
