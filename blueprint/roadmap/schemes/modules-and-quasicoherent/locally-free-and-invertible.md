---
article_id: af_0a1032d4064bbb5485d0d291
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Ringed.IsFree Hartshorne.Ringed.IsLocallyFree Hartshorne.Ringed.IsLocallyFreeOfRank Hartshorne.Ringed.IsInvertible Hartshorne.Ringed.rankAt Hartshorne.Ringed.rankAt_eq Hartshorne.Ringed.isLocallyConstant_rankAt Hartshorne.Ringed.rankAt_eq_of_connectedSpace AlgebraicGeometry.Scheme.Modules.isLocallyFree_iff_ringed AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_iff_ringed AlgebraicGeometry.Scheme.Modules.isInvertible_iff_ringed AlgebraicGeometry.Scheme.Modules.IsFree AlgebraicGeometry.Scheme.Modules.IsLocallyFree AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank AlgebraicGeometry.Scheme.Modules.IsInvertible AlgebraicGeometry.Scheme.Modules.rankAt AlgebraicGeometry.Scheme.Modules.rankAt_eq AlgebraicGeometry.Scheme.Modules.isLocallyConstant_rankAt AlgebraicGeometry.Scheme.Modules.rankAt_eq_of_connectedSpace AlgebraicGeometry.Scheme.Modules.rankAt_eq_ringed
---

# Locally free and invertible module sheaves

Define free and locally free $\mathcal{O} _X$-modules, locally free modules of a specified
finite rank, and invertible modules as the rank-one case.  On a ringed space
all of whose stalks $\mathcal{O} _{X,x}$ are nonzero rings (for instance any
locally ringed space, and so any scheme), show that the rank of a locally free
module is locally constant, hence constant when $X$ is connected.  The
hypothesis on the stalks is needed: if $\mathcal{O} _{X,x} = 0$, then
$\mathcal{O} _X$ vanishes on a neighbourhood of $x$, where every module is free
of every rank.

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- [Skyscraper module sheaves and the stalk adjunction](../module-stalks/module-skyscraper-stalk-adjunction.md)
- Invariant basis number for nonzero commutative rings.

## Sources

- [Hartshorne II.5, free, locally free, and invertible sheaves on printed p. 109](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
