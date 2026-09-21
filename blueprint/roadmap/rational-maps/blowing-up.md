---
article_id: af_4d390f0993f2c69e8e37f37c
declaration: theorem
origin: cited
source_units: [chapter-i-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.blowing_up
---

# Blowing up a point

The *blowing-up of `𝔸ⁿ` at the origin* is the closed subset

`X = { (x, y) ∈ 𝔸ⁿ × ℙⁿ⁻¹ : xᵢyⱼ = xⱼyᵢ for all i, j }`,

together with the morphism `φ : X → 𝔸ⁿ` restricting the first projection. For a
closed subvariety `Y ⊆ 𝔸ⁿ` through the origin `O`, the *blowing-up of `Y` at
`O`* is `Ỹ = closure(φ⁻¹(Y − O))`, with `φ : Ỹ → Y` the restriction. Blowing up
at any other point is a linear change of coordinates away.

This is the last construction of the section and the standard example of a
birational morphism that is not an isomorphism. It is also the tool resolution
of singularities is built from, which is why Hartshorne includes it here rather
than leaving it to the exercises.

## What is claimed

The formal statement treats the origin in a finite nonempty affine coordinate
space over an algebraically closed field. It constructs the incidence locus
and proves all four properties below. For every affine variety `Y` through the
origin it records the exhaustive edge-case split: if `Y − {O}` is nonempty,
the strict transform is quasi-projective and birational to `Y`; otherwise
`Y = {O}` and the displayed strict transform is empty. Thus Hartshorne's
birationality sentence is formalized in precisely its nondegenerate case,
while its omitted zero-dimensional exception is made explicit.

Moving the centre by a linear change of coordinates, the general criterion
that a blow-up of a singular variety is not an isomorphism, and the detailed
calculation for the nodal cubic are context rather than claims of this node.

## The four properties of `X`

1. For `P ≠ O`, `φ⁻¹(P)` is a single point, and `φ` restricts to an isomorphism
   `X − φ⁻¹(O) ≅ 𝔸ⁿ − O`. Given `P = (a₁,…,a_n)` with `a_i ≠ 0`, the equations
   force `yⱼ = (aⱼ/aᵢ) yᵢ`, so `y = (a₁,…,a_n)` up to scalar. The inverse
   morphism is `P ↦ P × (a₁,…,a_n)`.
2. `φ⁻¹(O) ≅ ℙⁿ⁻¹`: the equations are vacuous when `x = 0`, so the fibre is all
   of `ℙⁿ⁻¹`.
3. Points of `φ⁻¹(O)` correspond to lines through `O` in `𝔸ⁿ`. The line
   `xᵢ = aᵢt` lifts to `xᵢ = aᵢt, yᵢ = aᵢ`, and those equations still make sense
   at `t = 0`, meeting `φ⁻¹(O)` in the point `(a₁,…,a_n) ∈ ℙⁿ⁻¹`.
4. `X` is irreducible. It is the union of `X − φ⁻¹(O)`, isomorphic to `𝔸ⁿ − O`
   and so irreducible, and `φ⁻¹(O)`; by (3) every point of `φ⁻¹(O)` lies in the
   closure of a line inside the first piece, so the first piece is dense.

Then `φ` induces an isomorphism `Ỹ − φ⁻¹(O) ≅ Y − O`, so `φ : Ỹ → Y` is a
birational morphism. As motivation, Hartshorne explains that it is not an
isomorphism when `Y` is singular at `O`: Example 4.9.1 blows up the plane cubic
`y² = x²(x + 1)` at the origin and finds that the two branches, which met at
`O`, are pulled apart to the two points `u = ±1` of the exceptional curve,
their slopes.

Hartshorne notes that the construction looks as though it depends on the
embedding `Y ⊆ 𝔸ⁿ` and remarks that it does not, referring forward to II.7.15.1.
That is out of scope and is not claimed.

## Depends on

- [Products of varieties](product-variety.md)
- [Birational maps](birational-map.md)
- [Morphisms](../morphisms/morphism.md)

## Proof depends on

- [Morphisms agreeing on an open set](morphism-agreement.md)
- [Criterion for a morphism to an affine variety](../morphisms/morphism-to-affine-criterion.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Sources

- [Hartshorne I.4, Blowing Up and Example 4.9.1 (pp. 28-29)](../../sources/hartshorne.md#i4)
