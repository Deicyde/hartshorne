---
declaration: theorem
origin: cited
---

# Criterion for a morphism into an affine variety

Let `X` be any variety and `Y ⊆ 𝔸ⁿ` an affine variety. A map of sets
`ψ : X → Y` is a morphism if and only if `xᵢ ∘ ψ` is regular on `X` for each
coordinate function `xᵢ` (Lemma 3.6).

Necessity is the definition. For sufficiency: if each `xᵢ ∘ ψ` is regular then so
is `f ∘ ψ` for every polynomial `f`, so `ψ⁻¹` of a closed set is closed and `ψ`
is continuous; and since regular functions on open subsets of `Y` are locally
quotients of polynomials, `g ∘ ψ` is regular for every regular `g`.

This is the workhorse of the section. Checking `n` regular functions is a finite,
concrete task, whereas checking the definition of a morphism quantifies over all
open sets and all regular functions on them. Every construction of a morphism
into affine space in Chapter I goes through it.

## Depends on

- [Morphisms](morphism.md)
- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, Lemma 3.6 (p. 20)](../../sources/hartshorne.md#i3)
