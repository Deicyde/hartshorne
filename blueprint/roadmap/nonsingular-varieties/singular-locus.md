---
article_id: af_881bbb9581972ab339f0acfd
declaration: theorem
origin: cited
source_units: [chapter-i-section-5-geometry]
---

# The singular locus is proper and closed

Let `X` be a separated variety over an algebraically closed field, equipped
with the affine-open-basis witness satisfied by Hartshorne's affine,
quasi-affine, projective, and quasi-projective varieties. Then

`SingularLocus X ⊊ X`

is a proper closed subset. This is Theorem 5.3.

Closedness is local on the affine-open basis. For properness, choose the natural
dimension `r` of `X` and apply Proposition 4.9 to obtain an irreducible
projective hypersurface birational to `X`. Corollary 4.5 supplies isomorphic
nonempty open subvarieties. Intersect the hypersurface-side open with a standard
affine chart: in that chart the hypersurface is defined by one irreducible
polynomial. Its nonsingular locus is nonempty open, so irreducibility makes its
intersection with the prescribed birational open nonempty. Nonsingularity
transfers across the open inclusions and the isomorphism because all the local
rings involved are isomorphic. The corresponding point of `X` is therefore
nonsingular, proving that its singular locus is not all of `X`.

## Depends on

- [Intrinsic nonsingularity](intrinsic-nonsingularity.md)
- [Open affine sets are a base for the topology](../rational-maps/affine-base.md)
- [Morphisms agreeing on an open set](../rational-maps/morphism-agreement.md)

## Proof depends on

- [Closedness from affine charts](singular-locus-closed.md)
- [An irreducible hypersurface has a nonsingular point](hypersurface-singular-locus-proper.md)
- [Every variety is birational to a hypersurface](../rational-maps/birational-hypersurface.md)
- [Birational varieties have isomorphic open subsets](../rational-maps/birational-open-subsets.md)
- [The standard affine charts](../projective-varieties/standard-affine-charts.md)
- [The charts are isomorphisms of varieties](../morphisms/projective-rings/chart-isomorphism.md)
- [Local rings are unchanged on open neighbourhoods](local-ring-open-invariance.md)

## Sources

- [Hartshorne I.5, Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)
