---
article_id: af_e6085b5482d318aaf9e1af13
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_isCoherent_restrict_iso_of_isNoetherian Hartshorne.exists_isCoherent_extension_of_isNoetherian
---

# Extension of coherent sheaves

Let $X$ be Noetherian, $U \subseteq X$ open, and $F$ coherent on $U$. There exists a
coherent sheaf $F'$ on $X$ with $F'|_U \cong F$. More precisely, if $G$ is a
quasi-coherent sheaf on $X$ such that $F \subseteq G|_U$ is a subsheaf, then there
is a coherent subsheaf $F' \subseteq G$ with $F'|_U = F$ as subsheaves of $G|_U$.

## Depends on

- [Coherent affine-local criterion](../modules-and-quasicoherent/coherent-affine-local-criterion.md)

## Proof depends on

- [Affine extension of coherent sheaves](coherent-extension-affine.md)
- A finite affine cover of the Noetherian scheme and induction extending over
  one affine open at a time.

## Sources

- [Hartshorne II.5, Exercise 5.15(d) (p.127)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
