---
declaration: def
origin: cited
---

# Projective algebraic sets

A homogeneous `f ∈ S` of degree `d` satisfies `f(λa) = λᵈ f(a)`, so whether
`f` vanishes at a point of `ℙⁿ` is well defined even though `f` is not a
function on `ℙⁿ`. For a set `T` of homogeneous elements put
`Z(T) = { P ∈ ℙⁿ : f(P) = 0 for all f ∈ T }`, and for a homogeneous ideal `𝔞`
put `Z(𝔞) = Z(T)` with `T` the homogeneous elements of `𝔞`. A subset of `ℙⁿ` is
an *algebraic set* when it is such a `Z(T)`.

Proposition 2.1 records the closure properties: finite unions and arbitrary
intersections of algebraic sets are algebraic, and `∅` and `ℙⁿ` are algebraic.
Hartshorne leaves the proof to the reader as it copies Proposition 1.1.

Since `S` is Noetherian, every `Z(T)` is `Z(f₁,…,f_r)` for finitely many
homogeneous `fᵢ`; that reduction is used whenever a hypersurface argument needs
a single equation.

## Depends on

- [Projective space](projective-space.md)
- [Homogeneous ideals](homogeneous-ideal.md)

## Sources

- [Hartshorne I.2, zero sets of homogeneous elements and Proposition 2.1 (p. 9)](../../sources/hartshorne.md#i2)
