---
article_id: af_fd6237e40274d9342ff299cf
declaration: structure
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety
---

# Varieties

Hartshorne calls an affine, quasi-affine, projective, or quasi-projective
variety over $k$ a *variety*. Each carries an irreducible topology and,
on every open subset, a $k$-algebra of regular functions.

Regular functions restrict to smaller opens; their zero loci are closed;
division by a nowhere-zero regular function preserves regularity; and
regularity is local. These properties give a common language for the
four types of varieties.

The identity principle follows from this structure. If two regular
functions agree on a nonempty open subset, their difference has a closed
zero locus containing that dense open subset, so they agree everywhere.
It is the principle used to compare germs and rational-function
representatives.

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, definition of a variety over $k$ (p. 15)](../../sources/hartshorne.md#i3)
