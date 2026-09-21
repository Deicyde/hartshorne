---
article_id: af_80387e069a7fe6f488ba819e
declaration: theorem
origin: bridged
source_units: [chapter-i-section-5-geometry]
---

# Rank-drop loci are determinantal

Let `M` be a finite matrix whose entries are polynomials on `𝔸ⁿ`, and let
`q : ℕ`. The points `P` for which the evaluated matrix `M(P)` has rank less
than `q` are exactly the common zero set of all `q × q` minors of `M`.
Consequently this rank-drop locus is Zariski closed.

The algebraic statement is the standard rank/minor criterion over a field:
rank at least `q` is equivalent to one `q × q` submatrix having nonzero
determinant. Evaluation commutes with determinants, so each evaluated minor is
the value at `P` of a polynomial determinant. Negating the existential gives a
simultaneous zero locus. The edge case `q = 0` is included: the empty minor has
determinant one and the rank-drop locus is empty.

This node is deliberately general rather than Jacobian-specific. It isolates
the finite matrix and determinant bookkeeping from the geometric argument in
Theorem 5.3.

## Depends on

- [The Zariski topology on affine space](../affine-varieties/zariski-topology.md)

## Sources

- [Hartshorne I.5, determinantal description in the proof of Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)
