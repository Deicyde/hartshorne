---
article_id: af_ae2f3f77382fd38d7e6b7097
declaration: example
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_isCoherent_not_isCoherent_pushforward
---

# A coherent pushforward counterexample

There exist varieties $X$ and $Y$ over a field, a morphism $f : X \to Y$, and
a coherent sheaf $F$ on $X$ such that $f_*F$ is not coherent on $Y$.

Use the structure morphism $A^1_k \to \operatorname{Spec} k$ and $F = \mathcal{O}_{A^1}$: the direct
image corresponds to the infinite-dimensional $k$-module $k[t]$. This is the
warning required by Caution 5.8.1; later positive pushforward results must
retain their finite, projective, or proper hypotheses.

## Depends on

- [Direct image of module sheaves](../modules-and-quasicoherent/module-push-pull-adjunction.md)
- [Coherent affine-local criterion](../modules-and-quasicoherent/coherent-affine-local-criterion.md)

## Sources

- [Hartshorne II.5, Exercise 5.5(a) and Caution 5.8.1 (pp.115,124)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
