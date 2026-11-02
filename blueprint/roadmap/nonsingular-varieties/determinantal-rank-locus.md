---
article_id: af_80387e069a7fe6f488ba819e
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.rank_lt_iff_forall_minors_eq_zero Hartshorne.matrixRankDropLocus_eq_zeroSet Hartshorne.isClosed_matrixRankDropLocus Hartshorne.determinantalMinors_zero Hartshorne.matrixRankDropLocus_zero
---

# Rank-drop loci are determinantal

Let $k$ be a field and let $M$ be a finite matrix whose entries are
polynomials in finitely many affine coordinates. For a nonnegative
integer $q$, the points where the evaluated matrix has rank below $q$
are exactly the common zero set of its $q\times q$ minors. Thus this
rank-drop locus is Zariski closed.

Over a field, rank at least $q$ is equivalent to the existence of a
nonzero $q\times q$ minor. Evaluation commutes with determinants, so
negating this condition gives the simultaneous vanishing of polynomial
minors. For $q=0$, the empty minor has determinant one and the rank-drop
locus is empty.

## Depends on

- [The Zariski topology on affine space](../affine-varieties/zariski-topology.md)

## Sources

- [Hartshorne I.5, determinantal description in the proof of Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)
