---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_dim_zeroSet_irreducible Hartshorne.exists_irreducible_eq_zeroSet
---

# Hypersurfaces and codimension one

A variety `Y ⊆ 𝔸ⁿ` has dimension `n − 1` if and only if `Y = Z(f)` for a single
nonconstant irreducible polynomial `f ∈ A` (Proposition 1.13).

The two directions came out asymmetric, and only one of them needs what
Hartshorne says it needs.

**Forward.** He goes through Krull's Hauptidealsatz: `(f)` is prime of height
one, and the dimension formula converts that into dimension `n − 1`. None of
that is required here. The Nullstellensatz gives `I(Z(f)) = (f)`, since a prime
is radical; Proposition 1.7 makes `dim Z(f)` the Krull dimension of
`k[x]/(f)`; Theorem 1.8A(a) makes that a transcendence degree; and
[the hypersurface computation](polynomial-hypersurface-trdeg.md) — built for the
dimension formula, not for this — says cutting by an irreducible drops it by
one. So the forward direction never mentions height.

**Backward.** Here the dimension formula is used in earnest: it turns
`dim A(Y) = n − 1` into `height I(Y) = 1`, and a height-one prime of a unique
factorisation domain is principal, its generator irreducible.

The two quoted results are in Mathlib. Hartshorne's Proposition 1.12A is
`UniqueFactorizationMonoid.isPrincipal_of_height_eq_one`, used in the backward
direction. His Theorem 1.11A, the Hauptidealsatz, turned out not to be needed by
either direction.

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
