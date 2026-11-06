---
article_id: af_1d46aac6dba6470680974531
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.varietyRestrictedSheafIso Hartshorne.varietyRestrictedPresheafIso Hartshorne.varietyClosedPointsInclusion Hartshorne.varietyClosedPointsTopIso
---

# Restricting the structure sheaf recovers regular functions

Let $V$ be a variety over an algebraically closed field and identify it with
the closed-point subspace of its associated scheme via $\alpha _V$.  The inverse
image of the associated scheme's structure sheaf along this homeomorphism is
canonically isomorphic to the original sheaf of regular functions on $V$.

The unique main artifact is this sheaf isomorphism.  For corresponding opens,
the associated scheme's sheaf was defined as $\alpha _{V\cdot }\mathcal{O} _V$, so its sections and
restriction maps agree with those of $\mathcal{O} _V$; sheaf extensionality assembles
these componentwise identifications.

## Depends on

- [The regular-function sheaf on the generic completion](generic-completion-sheaf.md)
- [Classical points are the closed points](variety-closed-points.md)
- [The sheaf of regular functions](../sheaves/regular-functions-sheaf.md)

## Sources

- [Hartshorne II.2, restricted-sheaf clause of Proposition 2.6 (p. 78)](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)
