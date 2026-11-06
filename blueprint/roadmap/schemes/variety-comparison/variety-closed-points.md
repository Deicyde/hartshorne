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

Here, as for the associated scheme itself, $V$ has an affine-open basis.  The
residue field of a point $z$ is $k$ when the composite
$k \to \Gamma (t(V),\mathcal{O} ) \to \mathcal{O} _{t(V),z} \to \kappa (z)$ of the
constant regular functions, the germ map and the residue map is bijective.

In $t(V)$ an irreducible closed subset $Z'$ lies in the closure of the point
$Z$ exactly when $Z' \subseteq Z$, so $Z$ is a closed point exactly when it is a
minimal irreducible closed subset.  On an affine open neighbourhood the
coordinate functions are regular and separate points, and their non-vanishing
loci are open; hence the points of $V$ are closed, and the closed points of
$t(V)$ are exactly the points $\alpha _V(P) = \{P\}$.  The topology is the
subspace topology because $\alpha _V$ induces the established bijection on open
sets: the preimage of the set of irreducible closed subsets meeting an open
$U \subseteq V$ is $U$.

Exercise 2.15(a) gives the intrinsic residue-field characterization.  At
$\alpha _V(P)$, evaluation at $P$ is a ring map
$\mathcal{O} _{t(V),\alpha _V(P)} \to k$ fixing constants, so every germ differs
from a constant by a non-unit and the residue field is $k$.  Conversely, if $Z$
is not a point, it meets an affine open $U$ in two points separated by a
coordinate function $f$.  For every $c \in k$, the function $f - c$ is invertible
on the open set where it does not vanish, which meets $Z$; so the germ of
$f - c$ at $Z$ is a unit, and the residue class of $f$ is not a constant.

## Depends on

- [A variety with an affine-open basis has an associated scheme](variety-associated-scheme.md)
- [The associated scheme is a scheme over the base field](variety-scheme-over-k.md)

## Proof depends on

- [Field-valued points of a scheme](../foundational-properties/field-valued-points.md)
- [Points and maximal ideals](../../morphisms/points-eq-maximal-ideals.md)

## Sources

- [Hartshorne II.2, closed-point clause of Proposition 2.6 and Exercise 2.15(a) (pp. 78–81)](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
