---
declaration: def
origin: cited
---

# Affine and quasi-affine varieties

A nonempty subset `Y` of a topological space is *irreducible* when it is not the
union of two proper subsets each closed in `Y`; the empty set is excluded by
convention. An *affine variety* is an irreducible closed subset of `𝔸ⁿ` with the
induced topology, and a *quasi-affine variety* is a nonempty open subset of an
affine variety.

Mathlib's `IsIrreducible` matches Hartshorne's notion, including the exclusion
of `∅`. The definitional work is packaging affine and quasi-affine varieties as
types carrying their induced topology, in a form that §3 can put a sheaf of
regular functions on and that §2 can compare with the projective case.

Recording the choice explicitly: Hartshorne's varieties are always irreducible,
so `Z(f)` for a reducible `f` is an algebraic set and not a variety. Every
statement in this roadmap keeps that convention, since dropping it silently
changes what `K(Y)` and `dim Y` mean.

## Depends on

- [The Zariski topology on affine space](zariski-topology.md)

## Sources

- [Hartshorne I.1, definitions of irreducible, affine variety and quasi-affine variety (p. 3)](../../sources/hartshorne.md#i1)
