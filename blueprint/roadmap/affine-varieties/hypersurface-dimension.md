---
declaration: theorem
origin: cited
---

# Hypersurfaces and codimension one

A variety `Y ⊆ 𝔸ⁿ` has dimension `n − 1` if and only if `Y = Z(f)` for a single
nonconstant irreducible polynomial `f ∈ A` (Proposition 1.13).

Forward: `A` is a UFD, so an irreducible `f` generates a prime ideal, that prime
has height `1` by Krull's Hauptidealsatz, and Theorem 1.8A converts height `1`
into dimension `n − 1`. Backward: a variety of dimension `n − 1` corresponds to a
height-one prime, which in a UFD is principal, and its generator is irreducible.

Two quoted results are used and both are already in the pinned Mathlib:
Hartshorne's Theorem 1.11A is
`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`, and his Proposition
1.12A is `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`.
Neither needs its own node; check the exact hypotheses when wiring them in,
since Mathlib states the height bound as an inequality.

## Depends on

- [Affine and quasi-affine varieties](affine-variety.md)
- [Dimension of a topological space and of a ring](dimension.md)
- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](dim-formula-catenary.md)

## Sources

- [Hartshorne I.1, Theorem 1.11A, Proposition 1.12A and Proposition 1.13 (p. 7)](../../sources/hartshorne.md#i1)
