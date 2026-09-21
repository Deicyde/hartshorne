---
article_id: af_216e8eb4b2cf660392e118b5
declaration: theorem
origin: cited
source_units: [chapter-i-section-5-geometry]
statement: formalized
proof: formalized
lean: Hartshorne.exists_affineNonsingularAt_zeroSet_irreducible Hartshorne.exists_nonsingularAt_of_eq_zeroSet_irreducible Hartshorne.hypersurface_singularLocus_isProper Hartshorne.hypersurface_zeroSet_singularLocus_isProper
---

# An irreducible hypersurface has a nonsingular point

Let `f ∈ k[x₁,…,xₙ]` be irreducible and nonconstant, and let
`Y = Z(f) ⊆ 𝔸ⁿ`. Then `SingularLocus Y` is a proper closed subset of
`Y`; equivalently the nonsingular locus is a nonempty open subset.

Closedness is the affine determinantal theorem. If every point were singular,
the one-row Jacobian of the hypersurface would have rank zero everywhere, so
each `∂f/∂xᵢ` would vanish on `Y`. The Nullstellensatz puts every partial in
`I(Y) = (f)`. Since its degree is strictly less than `deg f`, each partial must
be zero, contradicting the fact that an irreducible nonconstant polynomial over
an algebraically closed field has a nonzero partial.

The statement includes the open-locus conclusion because the proof of the
general case must intersect it with a prescribed nonempty birational open set.

## Depends on

- [Intrinsic nonsingularity](intrinsic-nonsingularity.md)

## Proof depends on

- [The affine singular locus is closed](affine-singular-locus-closed.md)
- [An irreducible polynomial has a nonzero partial derivative](irreducible-polynomial-nonzero-partial.md)
- [Hilbert's Nullstellensatz](../affine-varieties/nullstellensatz.md)
- [Hypersurfaces and codimension one](../affine-varieties/hypersurface-dimension.md)

## Sources

- [Hartshorne I.5, hypersurface case of Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)
