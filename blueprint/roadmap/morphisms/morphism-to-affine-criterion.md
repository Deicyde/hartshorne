---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_varietyHom_iff_coords_regular Hartshorne.regular_comp_of_coords_regular Hartshorne.Variety.continuous_of_coords_regular Hartshorne.Variety.eval_comp_mem_regular
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

## What it cost the `Variety` structure

Hartshorne states Lemma 3.6 for an arbitrary source `X`, and the project's
bundled `Variety` was too weak to support that. It carried a `k`-subalgebra of
regular functions per open subset plus restriction, and the proof needs three
things a subalgebra does not give:

- zero loci of regular functions are closed, for continuity;
- closure under division by a nowhere-zero regular function; and
- locality,

because the pullback of a regular function is only *locally* a quotient of
pulled-back polynomials. All three hold in each of Hartshorne's four cases,
where regularity is *defined* by the local-quotient condition, and all three are
now fields, discharged by Lemma 3.1 and by the pointwise definition. See
[Varieties](variety.md).

The statement here allows a quasi-affine target rather than only an affine one.
Nothing in the argument uses closedness of `Y`, and the extra generality is what
Proposition 3.5 will want.

## Depends on

- [Morphisms](morphism.md)
- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, Lemma 3.6 (p. 20)](../../sources/hartshorne.md#i3)
