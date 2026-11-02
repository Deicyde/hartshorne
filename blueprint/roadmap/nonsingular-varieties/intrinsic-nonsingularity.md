---
article_id: af_2ff2bb8fe76379abcf802044
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.NonsingularAt Hartshorne.Variety.Nonsingular Hartshorne.Variety.SingularLocus Hartshorne.Variety.Singular
---

# Intrinsic nonsingularity

A variety $X$ is *nonsingular at* $P$ if its local ring
$\mathcal O_{P,X}$ is regular. It is nonsingular if this holds at every
point. Its *singular locus* is the set of points where the local ring is
not regular.

These are Hartshorne's intrinsic definitions after Theorem I.5.1.
For an affine variety, the Jacobian criterion gives the equivalent
coordinate definition. Passing to an open neighbourhood leaves the
local ring unchanged, so nonsingularity is local. An isomorphism of
varieties carries nonsingular points to nonsingular points because it
induces isomorphisms of local rings.

## Depends on

- [The Jacobian criterion](jacobian-criterion.md)
- [Local rings are unchanged on open neighbourhoods](local-ring-open-invariance.md)
- [The local ring at a point](../morphisms/local-ring.md)

## Proof depends on

- [The local ring is functorial](../morphisms/local-ring-functorial.md)

## Sources

- [Hartshorne I.5, intrinsic definitions of nonsingular and singular varieties (p. 32)](../../sources/hartshorne.md#i5)
