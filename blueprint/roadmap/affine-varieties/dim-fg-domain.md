---
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.isAlgebraic_of_isFractionRing Hartshorne.exists_ringKrullDim_eq_trdeg
---

# Dimension of a finitely generated domain

Let `k` be a field and `B` an integral domain that is a finitely generated
`k`-algebra. Then `dim B = trdeg_k K(B)`, the transcendence degree of the
fraction field.

This is the first clause of Hartshorne's Theorem 1.8A, quoted from Matsumura and
Atiyah–Macdonald. Everything numerical in Chapter I rests on it, together with
its second clause, which is now
[the dimension formula](dim-formula-catenary.md): `dim 𝔸ⁿ = n`, `dim Y = dim Ȳ`
for quasi-affine `Y`, the codimension-one characterisation of hypersurfaces, and
in §3 the fact that `K(Y)` has transcendence degree `dim Y`.

Because it is quoted rather than proved in the source, the proof is not
constrained to follow Hartshorne. A single Noether normalisation
`k[y₁,…,y_s] ↪ B` answers both sides: `B` is integral over the polynomial ring,
so the two have the same dimension, and it is algebraic over it, so they have
the same transcendence degree. The fraction field is algebraic over `B`, so it
does not move the transcendence degree either.

## Statement shape

`ringKrullDim` is valued in `WithBot ℕ∞` and `Algebra.trdeg` in `Cardinal`,
which have no canonical map between them. The statement is therefore that one
natural number `s` answers both questions, which is what the equation means and
is strictly more informative, since it also records that both sides are finite.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)
- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)
- [A finitely generated algebra over a field has finite dimension](dim-fg-algebra-finite.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
