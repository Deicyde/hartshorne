---
article_id: af_1f107512e01c4032a330c528
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.projective_inter_nonempty_of_dim
---

# Projective varieties of complementary dimension meet

Let `Y,Z ⊆ ℙⁿ` be projective varieties of natural dimensions `r,s`.  If
`n ≤ r + s`, then `Y ∩ Z` is nonempty.  The sole main declaration is planned
as `Hartshorne.projective_inter_nonempty_of_dim`.

The cones `C(Y)` and `C(Z)` are affine varieties of dimensions `r+1` and
`s+1` in `𝔸ⁿ⁺¹`, and both contain the origin.  Apply the affine dimension
theorem to a component of their intersection.  Under `n ≤ r+s`, that component
has positive dimension, so it cannot be the singleton origin and contains a
nonzero point.  Projectivizing that point produces a point of `Y ∩ Z`.

The dimension hypotheses should be recorded as natural witnesses
`projDim Y = r` and `projDim Z = s`; this avoids truncated subtraction and
keeps the source's condition literal.

## Depends on

- [The affine cone and its ideal](affine-cone-ideal.md)
- [Irreducibility of the affine cone](affine-cone-irreducible.md)
- [Dimension of the affine cone](affine-cone-dimension.md)
- [The affine dimension theorem](affine-dimension-theorem.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](../../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne I.7, second clause of Theorem 7.2 (pp. 48--49)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
