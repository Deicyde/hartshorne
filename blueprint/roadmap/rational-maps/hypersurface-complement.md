---
declaration: theorem
origin: cited
---

# The complement of a hypersurface is affine

Let `Y = Z(f)` be the hypersurface in `𝔸ⁿ` cut out by `f ∈ k[x₁,…,x_n]`. Then
`𝔸ⁿ − Y` is isomorphic to the hypersurface `H = Z(x_{n+1} f − 1)` in `𝔸ⁿ⁺¹`. In
particular `𝔸ⁿ − Y` is affine, with coordinate ring `k[x₁,…,x_n]_f`
(Lemma 4.2).

An open set is not usually affine, so this is a genuine construction and not a
formality: the trick is to buy the missing inverse of `f` by paying for one more
coordinate.

## The proof

Projection `π : H → 𝔸ⁿ`, `(a₁,…,a_{n+1}) ↦ (a₁,…,a_n)`, is a morphism, being
given by coordinate functions. It corresponds to the ring map `A → A_f` for
`A = k[x₁,…,x_n]`, since on `H` the last coordinate is forced to be `1/f`. It is
a bijection onto `𝔸ⁿ − Y`: a point off `Y` has `f ≠ 0` there, so there is one
and only one legal value of `x_{n+1}`.

Bijectivity is not enough — a bijective morphism need not be an isomorphism — so
the inverse has to be exhibited as a morphism. It is
`(a₁,…,a_n) ↦ (a₁,…,a_n, 1/f(a₁,…,a_n))`, whose last coordinate is a regular
function on `𝔸ⁿ − Y` precisely because `f` is invertible there. Lemma 3.6, the
criterion that a map to an affine variety is a morphism as soon as its
coordinates are regular, is what turns that observation into a morphism.

The coordinate ring is then read off: `A(H) = k[x₁,…,x_{n+1}]/(x_{n+1} f − 1)`,
which is `A_f` because inverting `f` is exactly adjoining a root of
`x_{n+1} f − 1`.

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)
- [Morphisms](../morphisms/morphism.md)

## Proof depends on

- [Criterion for a morphism to an affine variety](../morphisms/morphism-to-affine-criterion.md)
- [Isomorphism via coordinate rings](../morphisms/affine-iso-iff-algebra-iso.md)
- [Hypersurfaces and codimension one](../affine-varieties/hypersurface-dimension.md)

## Sources

- [Hartshorne I.4, Lemma 4.2 (p. 25)](../../sources/hartshorne.md#i4)
