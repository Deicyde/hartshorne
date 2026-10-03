---
article_id: af_48c7c4f5e9b312d11ea4f08a
declaration: definition
origin: bridged
source_units: [chapter-i-section-2, chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.projectiveComponents Hartshorne.mem_projectiveComponents Hartshorne.iUnion_projectiveComponentCarrier_eq Hartshorne.iUnion_projectiveComponents_eq
---

# Projective algebraic sets are finite unions of their components

For a projective algebraic set `Y`, package the irreducible components of the
subspace `Y` as a finite set `projectiveComponents Y`.  Every component has an
ambient carrier which is a projective variety, every point of `Y` belongs to
one of these carriers, and their union is exactly `Y`.

The unique main declaration is the finite package `projectiveComponents Y`.
The membership and two carrier-cover equalities are supporting API. Hartshorne
Exercise 2.5(b) supplies the projective finite irreducible decomposition;
Remark 7.8.2 is the downstream use that requires it.

## Depends on

- [Projective and quasi-projective varieties](../../projective-varieties/projective-variety.md)
- [Projective space is a Noetherian space](../../projective-varieties/projective-space-noetherian.md)
- [Projective intersection components on an affine chart](../dimension/projective-intersection-components.md)

## Sources

- [Hartshorne I.2, Exercise 2.5(b) (p. 11)](../../../sources/hartshorne.md#i2)
- [Hartshorne I.7, Remark 7.8.2 (p. 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
