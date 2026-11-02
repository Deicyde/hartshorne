---
article_id: af_3f6ebf4555248edb9ac0b577
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.IsRegularAtProjVia Hartshorne.IsRegularProjVia Hartshorne.IsRegularProj
---

# Regular functions on a quasi-projective variety

Let $Y\subseteq\mathbb P^n$ be quasi-projective. A function $f:Y\to k$
is *regular at* $P$ if there is an open neighbourhood $U$ of $P$ in $Y$
and homogeneous polynomials $g,h$ of the same degree, with $h$ nowhere
zero on $U$, such that $f=g/h$ on $U$.

The equal-degree condition makes the ratio independent of homogeneous
coordinates: the common scaling factor cancels. Continuity and the identity
principle follow by the same local quotient argument as in the quasi-affine
case.

## Depends on

- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Sources

- [Hartshorne I.3, definition of a regular function on a quasi-projective variety (p. 15)](../../sources/hartshorne.md#i3)
