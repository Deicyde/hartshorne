---
article_id: af_105e5c9ea0f8b6df2e6d90c7
declaration: definition
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.reduciblePlaneCurveIntersectionMultiplicity
---

# Pointwise multiplicity for reducible plane curves

Let $Y,Z\subseteq\mathbb P^2$ be projective algebraic sets of dimension
one, with every irreducible component of dimension one and no common
component. Thus $C\ne D$ for every component $C$ of $Y$ and component
$D$ of $Z$.

For a point $P$ of the ambient plane, define

$$i(Y,Z;P)=\sum_C\sum_D\sum_{W\subseteq C\cap D}
\mathbf 1_{\{P\in W\}}\,i(C,D;W),$$

where the last sum is over irreducible components of $C\cap D$ and the
indicator is one when $P\in W$, zero otherwise. The value is a
nonnegative integer. Each such $W$ is a singleton, and $Y\cap Z$ is
finite. Summing over the intersection removes the indicators and gives
the corresponding finite triple sum of component multiplicities.

The dimension-one, purity and no-common-component hypotheses are not needed
for the defining sum to make sense, because every projective algebraic set has
finitely many irreducible components and the multiplicity
$i(C,D;W)=\mu_{\mathfrak p_W}\bigl(S/(I(C)+I(D))\bigr)$, with $S$ the
homogeneous coordinate ring of $\mathbb P^2$ and $\mathfrak p_W$ the
homogeneous prime of $W$, is defined for every component $W$ of $C\cap D$;
they are what make each $W$ a single point and $Y\cap Z$ finite, so that the
sum becomes a finite sum over the points of $Y\cap Z$.

This is a project-authored definition of the reindexing needed for the
extension asserted in Hartshorne's Remark I.7.8.2.

## Depends on

- [Projective algebraic sets are finite unions of their components](projective-components-finite-cover.md)
- [Intersection multiplicity with a hypersurface](projective-intersection-multiplicity.md)

## Proof depends on

- [Bézout's theorem for distinct plane curves](plane-curve-bezout.md)
- [Projective codimension one is a hypersurface](../dimension/projective-codimension-one-hypersurface.md)
- [Proper closed subsets of projective varieties have smaller dimension](../dimension/projective-proper-closed-dimension-drop.md)
- [Proper hypersurface sections are equidimensional](hypersurface-section-components-equidimensional.md)
- [A zero-dimensional projective variety is a point](projective-zero-dimensional-variety-point.md)

## Sources

- [Hartshorne I.7, Remark 7.8.2 (p. 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
