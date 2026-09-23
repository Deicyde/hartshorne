---
article_id: af_a79b80aca295435c1fad8a9f
declaration: theorem
origin: background
source_units: [theorem-i-3-9a]
---

# Finiteness of integral closure

Let `A` be a finitely generated algebra domain over the algebraically closed
field `k`, let `K` be its fraction field, and let `L/K` be a finite algebraic
extension.  If `A'` is the integral closure of `A` in `L`, then `A'` is a
finite `A`-module and therefore a finitely generated `k`-algebra.

This is Theorem 3.9A under the standing hypothesis on `k`, with no
separability assumption on `L/K`.  Choose a Noether normalization
`P = k[X_1,\ldots,X_n] → A`.  The extension `A/P` is integral, while `L`
is finite over the fraction field of `P`.  The integral elements of `L` over
`A` and over `P` coincide.  Finiteness of the normalization over `P` therefore
gives a finite `P`-spanning family, and the same family spans over the larger
ring `A`.

The finite-type conclusion over `k` should be exposed as a companion theorem
or instance. Hartshorne uses it in the proof of Corollary 6.6 to realize `A'`
as an affine coordinate ring; the independent two-chart implementation obtains
the corresponding finite-type fact from Mathlib's separable theorem instead.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Normalizations of polynomial rings are finite](polynomial-normalization-finite.md)

## Sources

- [Hartshorne I.3, Theorem 3.9A (p. 20)](../../sources/hartshorne.md#i3)
