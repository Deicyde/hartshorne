---
article_id: af_0bbdf1efed6dcc5ffe5d91e9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_isCoherent_restrict_iso Hartshorne.exists_isCoherent_extension Hartshorne.exists_finite_mem_spanSheaf Hartshorne.isCoherent_spanSheaf Hartshorne.spanSheaf
---

# Affine extension of coherent sheaves

Let $X$ be affine Noetherian, $U \subseteq X$ open, and $F$ coherent on $U$. Then
there is a coherent sheaf $F'$ on $X$ with $F'|_U \cong F$. More precisely, if
$G$ is a quasi-coherent sheaf on $X$ such that $F \subseteq G|_U$ is a subsheaf,
then there is a coherent subsheaf $F' \subseteq G$ with $F'|_U = F$ as subsheaves
of $G|_U$.

The auxiliary assertion that every quasi-coherent sheaf on an affine
Noetherian scheme is the directed union of its coherent subsheaves is included
as proof support.

## Depends on

- [Coherent affine-local criterion](../modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Quasi-coherence by local presentations](../modules-and-quasicoherent/quasicoherent-local-presentations.md)

## Proof depends on

- [Affine quasi-coherent equivalence](../modules-and-quasicoherent/affine-quasicoherent-equivalence.md)
- [Quasi-coherent pushforward](../modules-and-quasicoherent/qcqs-pushforward-quasicoherent.md)

## Sources

- [Hartshorne II.5, Exercise 5.15(a–c) (pp.126–127)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
