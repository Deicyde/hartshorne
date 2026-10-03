---
article_id: af_48c7c4f5e9b312d11ea4f08a
declaration: definition
origin: bridged
source_units: [chapter-i-section-7-main]
---

# Projective algebraic sets are finite unions of their components

For a projective algebraic set `Y`, package the irreducible components of the
subspace `Y` as a finite set `projectiveComponents Y`.  Every component has an
ambient carrier which is a projective variety, every point of `Y` belongs to
one of these carriers, and their union is exactly `Y`.

This is the finite indexing interface needed to apply irreducible results
componentwise to a reducible projective algebraic set.  The underlying
finiteness and coverage are the Noetherian-space irreducible-component
theorems; the new content is their projective ambient-space packaging.

## Depends on

- [Projective and quasi-projective varieties](../../projective-varieties/projective-variety.md)
- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne I.1, Proposition 1.5 and I.7, Remark 7.8.2](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
