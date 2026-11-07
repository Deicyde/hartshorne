---
article_id: af_f67cd2877cf877d4cfc3a585
declaration: def
origin: bridged
---

# Stalks of the pullback of a module sheaf

Let $h : X' \to X$ be a morphism of schemes, $F$ an $\mathcal{O}_X$-module, and
$x' \in X'$ with $x = h(x')$. Regard $\mathcal{O}_{X',x'}$ as an
$\mathcal{O}_{X,x}$-algebra through the stalk map $h^\#_{x'}$. There is an
isomorphism of $\mathcal{O}_{X',x'}$-modules

$(h^*F)_{x'} \cong \mathcal{O}_{X',x'} \otimes_{\mathcal{O}_{X,x}} F_x$,

natural in $F$.

As functors of $F$, both sides are left adjoint to the same functor, which
sends an $\mathcal{O}_{X',x'}$-module $N$ to a skyscraper sheaf at $x$. For
such $N$, a map $(h^*F)_{x'} \to N$ corresponds to a
morphism $h^*F \to i_{x'}(N)$, hence to a morphism $F \to h_* i_{x'}(N)$. The
direct image $h_* i_{x'}(N)$ is the skyscraper sheaf $i_x(N)$, with $N$ viewed
as an $\mathcal{O}_{X,x}$-module by restriction of scalars. So such maps
correspond to $\mathcal{O}_{X,x}$-linear maps $F_x \to N$, and by extension of
scalars to $\mathcal{O}_{X',x'}$-linear maps
$\mathcal{O}_{X',x'} \otimes_{\mathcal{O}_{X,x}} F_x \to N$. Uniqueness of
left adjoints gives the natural isomorphism. Equivalently, from Hartshorne's
definition $h^*F = h^{-1}F \otimes_{h^{-1}\mathcal{O}_X} \mathcal{O}_{X'}$, the
inverse image and the tensor product are both computed stalkwise.

## Depends on

- [Pushforward, pullback, and their adjunction](../modules-and-quasicoherent/module-push-pull-adjunction.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- [Skyscraper module sheaves and the stalk adjunction](module-skyscraper-stalk-adjunction.md)
- Extension of scalars along a ring homomorphism is left adjoint to
  restriction of scalars.
- The direct image of a skyscraper module sheaf at $x'$ is the skyscraper
  sheaf at $h(x')$ of the restricted module.

## Sources

- [Hartshorne II.5, definitions of direct and inverse image on printed pp.109–110](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
