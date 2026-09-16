---
declaration: theorem
origin: cited
---

# Products of varieties

Use [the Segre embedding](segre-embedding.md) to identify `ℙʳ × ℙˢ` with its
image, giving it the structure of a projective variety. For quasi-projective
`X ⊆ ℙʳ` and `Y ⊆ ℙˢ`, the subset `X × Y ⊆ ℙʳ × ℙˢ` is then a quasi-projective
variety, projective when `X` and `Y` are (Exercise 3.16(a),(b)). The two
projections are morphisms, and a pair of morphisms `Z → X`, `Z → Y` induces a
morphism `Z → X × Y`.

Adopted from §3 because the blowing-up construction is carried out inside
`𝔸ⁿ × ℙⁿ⁻¹`.

## What is claimed

Hartshorne's part (c), that `X × Y` is a product in the category of varieties,
is starred in the source. Only the part §4 consumes is claimed here: the
projections are morphisms and the universal arrow exists. Uniqueness of that
arrow is free once [Lemma 4.1](morphism-agreement.md) is available, but it is
not used.

The topology is the sticking point for a reader and deserves saying once: the
Zariski topology on `X × Y` is *not* the product of the Zariski topologies.
`ℙ¹ × ℙ¹` is a quadric surface in `ℙ³` containing curves that are not finite
unions of horizontal and vertical lines, so the product topology is strictly
coarser. Every statement here is about the topology induced from `ℙᴺ` through
the Segre embedding, and none of it would be true of the product topology.

*Closed.* For `X`, `Y` projective, `X × Y` is the intersection of the Segre
image with the zero sets of the bihomogeneous equations of `X` and `Y`, read in
the `z_ij`: a form `f(x)` of degree `d` times a form of degree `d` in `y`
becomes a form of degree `d` in the `z_ij`, so the conditions are homogeneous.

*Irreducible.* `X × Y` is covered by the affine pieces `(X ∩ Uᵢ) × (Y ∩ Vⱼ)`,
and an affine product is irreducible because `A(X) ⊗_k A(Y)` is a domain over an
algebraically closed field. Hartshorne gets this from Exercise 3.15(a) in the
affine case; the covering argument then glues the pieces, all of which meet.

*Projections and the universal arrow.* Both are checked chartwise, where the
Segre coordinates `z_ij` become ordinary affine coordinates and the criterion
for a morphism to an affine variety applies.

## Depends on

- [The Segre embedding](segre-embedding.md)
- [Morphisms](../morphisms/morphism.md)
- [Varieties](../morphisms/variety.md)

## Proof depends on

- [Varieties are covered by affine pieces](../projective-varieties/affine-cover.md)
- [Criterion for a morphism to an affine variety](../morphisms/morphism-to-affine-criterion.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Sources

- [Hartshorne I.3, Exercise 3.16 (p. 22)](../../sources/hartshorne.md#i4)
