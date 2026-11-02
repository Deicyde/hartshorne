---
article_id: af_809e3b45710db9e293c80345
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.isClosed_singularLocus_of_isIso Hartshorne.Variety.IsAffine.isClosed_singularLocus Hartshorne.Variety.HasAffineOpenBasis.isClosed_singularLocus
---

# Closedness from affine charts

Let $X$ be a variety carrying the affine-open-basis witness of Proposition 4.3.
Then the singular locus of $X$ is closed in $X$.

For each point choose an affine open neighbourhood $U$. Nonsingularity is
unchanged on passing from $X$ to $U$, because the two local rings at that point
are isomorphic. Transport an affine presentation of $U$; the preceding theorem
says that $\operatorname{Sing}(X)\cap U$, read in that presentation, is closed in $U$.
A subset is closed when its intersection with every member of an open cover is
closed in that member, so the affine pieces glue to the desired closed subset
of $X$.

The affine-open-basis hypothesis is kept explicit. An abstract variety with only regular-function algebras and irreducibility
need not have an affine-open basis.

## Depends on

- [Intrinsic nonsingularity](intrinsic-nonsingularity.md)
- [Open affine sets are a base for the topology](../rational-maps/affine-base.md)

## Proof depends on

- [The affine singular locus is closed](affine-singular-locus-closed.md)
- [Local rings are unchanged on open neighbourhoods](local-ring-open-invariance.md)

## Sources

- [Hartshorne I.5, local closedness argument in Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)
