---
declaration: theorem
origin: cited
---

# The Segre embedding

Let `N = rs + r + s`. The *Segre embedding* is

`ψ : ℙʳ × ℙˢ → ℙᴺ`, `(a₀,…,a_r) × (b₀,…,b_s) ↦ (…, aᵢbⱼ, …)`

in lexicographic order. It is well defined and injective, and its image is a
projective variety: writing `z_ij` for the homogeneous coordinates of `ℙᴺ` and
`𝔞` for the kernel of the `k`-algebra map `k[{z_ij}] → k[x₀,…,x_r, y₀,…,y_s]`
sending `z_ij` to `xᵢyⱼ`, the image is `Z(𝔞)` (Exercise 2.14).

Adopted from §2 because [products of varieties](product-variety.md) are what
give `𝔸ⁿ × ℙⁿ⁻¹` a meaning, and [blowing up](blowing-up.md) lives there.

## The three claims

*Well defined.* Rescaling `a` by `λ` and `b` by `μ` rescales every `aᵢbⱼ` by
`λμ`, so the image point of `ℙᴺ` is unchanged. The image vector is nonzero
because some `aᵢ` and some `bⱼ` are.

*Injective.* From the matrix `(aᵢbⱼ)` up to scalar, pick a nonzero entry
`a_pb_q`; then the `q`-th column recovers `a` up to scalar and the `p`-th row
recovers `b` up to scalar.

*Image is `Z(𝔞)`.* One inclusion is immediate: every element of `𝔞` vanishes on
the image by construction. The other is the calculation. A point of `Z(𝔞)` is a
matrix `(z_ij)`, not identically zero, satisfying in particular the relations
`z_ij z_lm − z_im z_lj ∈ 𝔞`, so all `2 × 2` minors vanish; a nonzero matrix of
rank one is a product of a column and a row, which is exactly a point of the
image. Since `𝔞` is prime — it is the kernel of a map into a domain — `Z(𝔞)` is
irreducible, so the image is a projective variety and not merely a closed set.

The relations `z_ij z_lm = z_im z_lj` generate `𝔞`, but that is not needed: the
rank-one argument only uses that they *lie* in `𝔞`.

## Depends on

- [Projective space](../projective-varieties/projective-space.md)
- [Projective algebraic sets](../projective-varieties/projective-algebraic-set.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Proof depends on

- [Algebraic sets and homogeneous radical ideals](../projective-varieties/homogeneous-ideal-correspondence.md)
- [Homogeneous ideals](../projective-varieties/homogeneous-ideal.md)

## Sources

- [Hartshorne I.2, Exercise 2.14 (p. 13)](../../sources/hartshorne.md#i4)
