---
declaration: theorem
origin: cited
---

# The dimension of affine space

`dim 𝔸ⁿ = n` (Proposition 1.9).

By the previous node this is the assertion that `k[x₁,…,xₙ]` has Krull dimension
`n`, which is Theorem 1.8A(a) applied to the polynomial ring: its fraction field
`k(x₁,…,xₙ)` has transcendence degree `n` over `k`.

Small as it is, this is the first place the whole dimension apparatus is used
end to end, and it is the sanity check that the definitions were set up
correctly. If `dim 𝔸ⁿ` comes out wrong the error is upstream, in the coercion
into `WithBot ℕ∞` or in the direction of the order isomorphism, not here.

## Depends on

- [Dimension is the dimension of the coordinate ring](dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](dim-fg-domain.md)

## Sources

- [Hartshorne I.1, Proposition 1.9 (p. 6)](../../sources/hartshorne.md#i1)
