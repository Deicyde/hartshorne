---
article_id: af_c57647eb59b0b19fca17b898
declaration: theorem
origin: cited
source_units: [chapter-i-section-5-geometry]
---

# The affine singular locus is closed

Let `Y ⊆ 𝔸ⁿ` be an affine variety of dimension `r`, and choose any
finite generating family of `I(Y)`. Its intrinsic singular locus is

`{P ∈ Y | rank J(P) < n − r}`.

It is therefore closed in `Y`; viewed in the ambient affine space it is the
algebraic set cut out by `I(Y)` together with all
`(n − r) × (n − r)` minors of the Jacobian matrix.

The Jacobian criterion identifies intrinsic nonsingularity with rank
`n − r`, and the rank bound rules out ranks above that value. The failure of
equality is consequently strict rank drop. Generator independence makes the
resulting subset intrinsic even though a chosen finite presentation supplies
the polynomial matrix used by the determinantal-locus theorem.

## Depends on

- [Intrinsic nonsingularity](intrinsic-nonsingularity.md)
- [Jacobian rank is independent of generators](jacobian-rank-invariance.md)

## Proof depends on

- [The Jacobian rank bound](jacobian-rank-upper-bound.md)
- [Rank-drop loci are determinantal](determinantal-rank-locus.md)

## Sources

- [Hartshorne I.5, closedness argument in Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)
