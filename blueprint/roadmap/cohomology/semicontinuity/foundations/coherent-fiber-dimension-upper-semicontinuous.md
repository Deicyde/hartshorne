---
article_id: af_7f3b0d6a9bc1810746558a00
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.moduleFiberDim Hartshorne.exists_nhds_moduleFiberDim_le_of_isCoherent Hartshorne.isClosed_setOf_le_moduleFiberDim_of_isCoherent
---

# Fibre dimension of a coherent sheaf is upper semicontinuous

Let $Y$ be a Noetherian scheme and $G$ a coherent $\mathcal{O}_Y$-module. The function

$y\mapsto\dim_{k(y)}\left(G_y\otimes_{\mathcal{O}_{Y,y}}k(y)\right)$

is upper semicontinuous: for every $y$ there is an open neighbourhood $U$
such that its value at every $y' \in U$ is at most its value at $y$.
Equivalently, for every integer $n$, the locus where the value is at least $n$
is closed.

The Noetherian hypothesis is not needed for this conclusion: coherence is
defined by a cover by affine opens on which the sheaf is associated to finitely
generated modules, and the argument only uses that the sections of $G$ over
every affine open are finitely generated, which holds for every coherent sheaf.

## Depends on

- [Coherent affine-local criterion](../../../schemes/modules-and-quasicoherent/coherent-affine-local-criterion.md)

## Proof depends on

- Nakayama's lemma identifies the fibre dimension with the minimal number of
  generators of $G_y$; a minimal generating set extends and generates on a
  neighbourhood because $G$ is coherent.

## Sources

- [Hartshorne III.12, Example 12.7.2, p.288](../../../../sources/hartshorne-iii-11-12.md#semicontinuity-grauert-and-base-change-pp287291)
