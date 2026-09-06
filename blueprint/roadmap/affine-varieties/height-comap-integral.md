---
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.height_le_height_comap_of_isIntegral Hartshorne.height_comap_le_height_of_hasGoingDown Hartshorne.height_comap_eq_height_of_isIntegral
---

# Height is preserved by contraction along an integral extension

Let `A ⊆ B` be an integral extension with `A` an integrally closed domain and
`B` a domain. Then a prime `𝔭` of `B` has the same height as `𝔭 ∩ A`.

This is the step [the dimension formula](dim-formula-catenary.md) needs in order
to move a prime of an affine domain down to a Noether normalisation, where it
becomes a prime of a polynomial ring and unique factorisation applies.

## Mathlib boundary

This was expected to be the large missing prerequisite, and it is not missing at
all: `Mathlib/RingTheory/IntegralClosure/GoingDown.lean` supplies exactly the
instance, for `R ⊆ S` integral with `S` a domain and `R` integrally closed. An
earlier search missed it because the instance is anonymous and lives under
`IntegralClosure` rather than beside the `HasGoingDown` class.

It applies to a Noether normalisation without any work: a polynomial ring over a
field is a unique factorisation domain, hence integrally closed, and the
normalisation is injective and integral.

## What was actually needed

Only the height statement that going down was wanted for:

`(𝔭 ∩ R).height = 𝔭.height`

(`Hartshorne.height_comap_eq_height_of_isIntegral`). One inequality contracts a
chain below `𝔭` and stays strictly increasing, because primes of an integral
extension over comparable primes are incomparable unless equal; the other lifts
a chain below `𝔭 ∩ R`, which is going down. Both directions are three lines once
the right Mathlib lemmas are named.

## Depends on

- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
