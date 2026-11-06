---
article_id: af_743d1a15c7f1fd1fc59e35c2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.varietyAssociatedSchemeAlpha Hartshorne.varietyAssociatedScheme_isEmbedding_alpha_and_range Hartshorne.varietyClosedPointsHomeomorph Hartshorne.varietyClosedPointsHomeomorph_apply Hartshorne.varietyAssociatedSchemeResidueConstants Hartshorne.varietyAssociatedScheme_isClosed_singleton_iff
---

# Classical points are the closed points

For a variety $V$ over an algebraically closed field $k$, the map
$\alpha _V : V \to t(V)$ is a homeomorphism from $V$ onto the subspace of closed
points of its associated scheme.  Equivalently, a point of $t(V)$ is closed if
and only if its residue field is $k$.

Here, as for the associated scheme itself, $V$ has an affine-open basis.

Reduce on affine opens to maximal ideals of $A(V)$; the Nullstellensatz
identifies them with classical points and residue field $k$.  The topology is
the subspace topology because $\alpha _V$ induces the established bijection on open
sets.  Exercise 2.15(a) gives the intrinsic residue-field characterization.

## Depends on

- [A variety with an affine-open basis has an associated scheme](variety-associated-scheme.md)
- [The associated scheme is a scheme over the base field](variety-scheme-over-k.md)

## Proof depends on

- [Field-valued points of a scheme](../foundational-properties/field-valued-points.md)
- [Points and maximal ideals](../../morphisms/points-eq-maximal-ideals.md)

## Sources

- [Hartshorne II.2, closed-point clause of Proposition 2.6 and Exercise 2.15(a) (pp. 78–81)](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
