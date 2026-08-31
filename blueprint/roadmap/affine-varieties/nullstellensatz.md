---
declaration: theorem
origin: background
mathlib: true
mathlib_declaration: MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
---

# Hilbert's Nullstellensatz

Let `k` be algebraically closed and `𝔞 ⊆ A = k[x₁,…,xₙ]` an ideal. If `f ∈ A`
vanishes at every point of `Z(𝔞)` then `fʳ ∈ 𝔞` for some `r > 0`; equivalently
`I(Z(𝔞)) = √𝔞`.

Hartshorne quotes this without proof (Theorem 1.3A) and uses it immediately for
Proposition 1.2(d). It is the only input that makes the algebraic-set / radical
ideal correspondence a bijection, and it is where algebraic closedness of `k`
enters: over `ℝ` the curve `x² + y² + 1 = 0` has no points and the statement
fails.

Mathlib proves it as `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` in
`Mathlib/RingTheory/Nullstellensatz.lean`, under
`[Field k] [Field K] [Algebra k K] [IsAlgClosed K] [Finite σ]`: the ideal lives
in `MvPolynomial σ k`, the zero locus in `σ → K`, and only the extension `K` is
required to be algebraically closed. Hartshorne's case is `K = k` with
`[IsAlgClosed k]` and `σ = Fin n`, which satisfies `[Finite σ]`. The work in this
node is checking that specialisation lines up, not reproving the theorem.

The `[Finite σ]` hypothesis is worth carrying forward: it is real, and it rules
out stating Chapter I over an arbitrary index type without extra work.

## Depends on

- [Algebraic sets](algebraic-set.md)
- [The vanishing ideal](vanishing-ideal.md)

## Sources

- [Hartshorne I.1, Theorem 1.3A and Proposition 1.2(d) (pp. 3-4)](../../sources/hartshorne.md#i1)
