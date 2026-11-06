---
article_id: af_40a97cd08eeda2135243a387
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_isFree_restrict_of_free_stalk Hartshorne.isLocallyFree_iff_forall_free_stalk
---

# The free locus of a coherent sheaf

Let $X$ be Noetherian and $F$ coherent. If $F_x$ is a free $\mathcal{O}_{X,x}$-module,
then $F$ is free on some open neighbourhood of $x$. Hence $F$ is locally free
if and only if every stalk $F_x$ is free.

No fixed rank is built into the theorem. Rank-constancy on connected
components belongs to the locally-free infrastructure.

## Depends on

- [Coherent affine-local criterion](../modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Locally free and invertible modules](../modules-and-quasicoherent/locally-free-and-invertible.md)

## Proof depends on

- The free locus of a finitely presented module is open, and finite presentation is preserved by localization.

## Sources

- [Hartshorne II.5, Exercise 5.7(a,b) (pp.124–125)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
