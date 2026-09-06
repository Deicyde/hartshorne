---
declaration: instance
origin: background
---

# Going down for an integral extension of a normal domain

Let `A ⊆ B` be an integral extension with `A` an integrally closed domain and
`B` a domain. Then going down holds: given primes `𝔮 ⊆ 𝔮'` of `A` and a prime
`𝔭'` of `B` over `𝔮'`, there is a prime `𝔭 ⊆ 𝔭'` of `B` over `𝔮`.

This is Atiyah–Macdonald 5.16, and it is the step
[the dimension formula](dim-formula-catenary.md) needs in order to compare the
height of a prime of an affine domain with the height of its contraction to a
Noether normalisation.

## Mathlib boundary

Mathlib has the class `Algebra.HasGoingDown` and the consequences the dimension
formula wants — in particular `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`,
which is exactly the comparison of heights across the extension. What it does
not have is an instance for this hypothesis: the only instance supplied is
`Algebra.HasGoingDown.of_flat`, and an integral extension is not flat in
general.

So the work here is to supply the instance, and the classical proof of it goes
through the integral closure of an ideal and a conjugation argument over the
fraction field. This is a self-contained piece of commutative algebra of a size
worth upstreaming, and it is a prerequisite rather than a part of Hartshorne.

## Depends on

- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
