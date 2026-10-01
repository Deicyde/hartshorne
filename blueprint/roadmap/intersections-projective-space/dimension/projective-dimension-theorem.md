---
article_id: af_2b64070bd52242f68017926b
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.projective_dimension_theorem
---

# The projective dimension theorem for components

Let `Y,Z ⊆ ℙⁿ` be projective varieties and let `W` be an irreducible component
of `Y ∩ Z`.  Then

`projDim Y + projDim Z ≤ projDim W + n`.

The sole main declaration is planned as
`Hartshorne.projective_dimension_theorem`.  For natural dimensions `r,s,t`,
this is the subtraction-free form of Theorem 7.2's assertion
`t ≥ r + s - n`.

Choose a standard affine chart meeting `W`.  The preceding chart-component
theorem turns `W` into a component of the intersection of the two affine chart
pieces and preserves all three dimensions.  Apply the affine dimension
theorem in that chart, whose ambient affine dimension is `n`.

## Depends on

- [The affine dimension theorem](affine-dimension-theorem.md)
- [Projective intersection components on an affine chart](projective-intersection-components.md)

## Sources

- [Hartshorne I.7, first clause of Theorem 7.2 (pp. 48--49)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
