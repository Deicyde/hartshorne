---
declaration: theorem
origin: cited
---

# The vanishing ideal

For `Y ⊆ 𝔸ⁿ` set `I(Y) = { f ∈ A : f(P) = 0 for all P ∈ Y }`, an ideal of `A`.
Proposition 1.2 records how `Z` and `I` interact:

- `T₁ ⊆ T₂` implies `Z(T₁) ⊇ Z(T₂)`;
- `Y₁ ⊆ Y₂` implies `I(Y₁) ⊇ I(Y₂)`;
- `I(Y₁ ∪ Y₂) = I(Y₁) ∩ I(Y₂)`;
- `Z(I(Y)) = Ȳ`, the Zariski closure of `Y`.

The main result is that `Z` and `I` form an antitone Galois connection between
ideals of `A` and subsets of `𝔸ⁿ`, with `Z ∘ I` the closure operator. Part (d)
of Hartshorne's Proposition 1.2, `I(Z(𝔞)) = √𝔞`, is the Nullstellensatz and is
stated separately.

Mathlib has `MvPolynomial.vanishingIdeal` and
`MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection`. The part not yet
present in that form is `Z(I(Y)) = Ȳ`, which needs the topology from this
chapter.

## Depends on

- [Algebraic sets](algebraic-set.md)
- [The Zariski topology on affine space](zariski-topology.md)

## Sources

- [Hartshorne I.1, definition of `I(Y)` and Proposition 1.2 (p. 3)](../../sources/hartshorne.md#i1)
