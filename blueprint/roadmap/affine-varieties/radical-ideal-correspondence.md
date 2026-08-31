---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.algebraicSetEquivRadicalIdeal Hartshorne.isIrreducible_iff_isPrime Hartshorne.isIrreducible_univ
---

# Algebraic sets and radical ideals

`Y ↦ I(Y)` and `𝔞 ↦ Z(𝔞)` are mutually inverse, inclusion-reversing bijections
between the algebraic sets in `𝔸ⁿ` and the radical ideals of `A`. Under this
bijection an algebraic set is irreducible if and only if its ideal is prime
(Corollary 1.4).

The bijection is formal from the Galois connection once the Nullstellensatz
supplies `I(Z(𝔞)) = √𝔞`. The irreducible-iff-prime half is the part with real
content and is the main result of this node: if `fg ∈ I(Y)` then `Y` is covered
by the two closed sets `Y ∩ Z(f)` and `Y ∩ Z(g)`, so irreducibility forces one
of them to be all of `Y`.

Two consequences Hartshorne draws immediately are worth proving here because
later sections cite them: `𝔸ⁿ` is irreducible, and every maximal ideal of `A` is
`(x₁ − a₁, …, xₙ − aₙ)` for a unique point `(a₁,…,aₙ)`.

## Depends on

- [The vanishing ideal](vanishing-ideal.md)
- [Hilbert's Nullstellensatz](nullstellensatz.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Sources

- [Hartshorne I.1, Corollary 1.4 with Examples 1.4.1 and 1.4.4 (p. 4)](../../sources/hartshorne.md#i1)
