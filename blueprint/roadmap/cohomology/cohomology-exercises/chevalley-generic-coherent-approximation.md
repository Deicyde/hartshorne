---
article_id: af_27e7f5a100771d1673bb38cc
declaration: theorem
origin: cited
lean: Hartshorne.exists_genericCoherentApproximation
statement: formalized
proof: formalized
---

# Generic coherent pushforward approximation

Let $f : X \to Y$ be a finite surjective morphism of integral Noetherian schemes,
let $M$ be a coherent module on $X$, and let $\alpha : \mathcal{O}_Y^r \to f_*M$, with
$r > 0$, be a map which is an isomorphism at the generic point of $Y$, as provided
by the generic finite-module frame. For every coherent module $F$ on $Y$ there are
a coherent module $G$ on $X$ and a morphism

$\beta : f_*G \longrightarrow F^{r}$

which is an isomorphism at the generic point of $Y$.

Surjectivity of $f$, integrality of $X$ and $r > 0$ are not used in the proof.

## Depends on

- [Finite morphisms](../../schemes/first-properties/finite-morphism.md)
- [A generic finite-module frame](chevalley-generic-finite-module-frame.md)

## Proof depends on

- [Finite pushforward preserves coherence](../../schemes/modules-and-quasicoherent/finite-pushforward-coherent.md)
- [The sheaf Hom of module sheaves](../../schemes/modules-and-quasicoherent/module-sheaf-hom.md)
- [Relative Spec of a quasi-coherent algebra](../../schemes/module-exercises/relative-spec.md).
  The needed half of (II, Ex. 5.17e) is proved directly: for affine $U \subseteq Y$,
  the $f_*\mathcal{O}_X(U)$-modules $\operatorname{Hom}_{\mathcal{O}_Y(U)}(f_*M(U), F(U))$
  glue to a coherent $\mathcal{O}_X$-module $G$ on $X = \operatorname{Spec}_Y f_*\mathcal{O}_X$,
  and $\beta$ is evaluation at the sections defining $\alpha$.
- Apply sheaf Hom into $F$ to the generic frame.
- (II, Ex. 5.17e), p.128: for affine $f$, $f_*$ is an equivalence from
  quasi-coherent $\mathcal{O}_X$-modules to quasi-coherent $f_*\mathcal{O}_X$-modules.
  Applied to $\mathcal{H}om(f_*M, F)$, with its $f_*\mathcal{O}_X$-action, it gives $G$.

## Sources

- [Hartshorne III, Exercise 4.2(b) (p.223)](../../../sources/hartshorne-iii-3-4.md#adopted-exercises-and-later-use)
- [External proof obligations](../../../sources/hartshorne-iii-3-4.md#external-proof-obligations)
