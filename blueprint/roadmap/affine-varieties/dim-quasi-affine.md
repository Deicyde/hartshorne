---
declaration: theorem
origin: cited
---

# Dimension of a quasi-affine variety

If `Y` is a quasi-affine variety then `dim Y = dim Ȳ` (Proposition 1.10).

One inequality is easy: closures of a chain of irreducible closed subsets of `Y`
form a chain in `Ȳ`. For the other, choose a maximal chain in `Y`, note that its
bottom term must be a point `P`, and read the chain in `A(Ȳ)` as primes
contained in the maximal ideal `𝔪_P`. Then `height 𝔪_P = n`, and since
`A(Ȳ)/𝔪_P ≅ k` has dimension `0`, the second half of Theorem 1.8A gives
`n = dim A(Ȳ) = dim Ȳ`.

This is the first proof in the chapter that genuinely needs the additivity
statement `height 𝔭 + dim B/𝔭 = dim B` rather than just the transcendence-degree
statement, which is worth knowing when scheduling the background node.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](dim-formula-catenary.md)
- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.1, Proposition 1.10 (p. 6)](../../sources/hartshorne.md#i1)
