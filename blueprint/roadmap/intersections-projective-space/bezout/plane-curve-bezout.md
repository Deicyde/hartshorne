---
article_id: af_bbb21dc5b1213e119c6d8a5d
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.plane_curve_bezout
---

# Bézout's theorem for distinct plane curves

Let `Y,Z ⊆ ℙ²` be distinct projective curves of degrees `d,e`. Their
intersection is a finite set `{P₁,…,Pₛ}`, and

`∑ j, i(Y,Z;P_j) = d·e`.

This is Corollary 7.8. Exercise 2.8 realizes `Z` as a hypersurface. Distinct
irreducible curves cannot contain one another, so Theorem 7.7 applies; the
projective dimension theorem makes the components points, each of degree one.

## Depends on

- [Bézout for a projective variety and a hypersurface](projective-hypersurface-bezout.md)

## Proof depends on

- [Projective codimension one is a hypersurface](../dimension/projective-codimension-one-hypersurface.md)
- [Proper closed subsets of projective varieties have smaller dimension](../dimension/projective-proper-closed-dimension-drop.md)
- [Hypersurface-section components are equidimensional](hypersurface-section-components-equidimensional.md)
- [A zero-dimensional projective variety is a point](projective-zero-dimensional-variety-point.md)
- [A projective point has Hilbert polynomial and degree one](projective-point-degree.md)

## Sources

- [Hartshorne I.7, Corollary 7.8 (p. 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
