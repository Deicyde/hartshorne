---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.restrictFunctionFieldEquiv Hartshorne.chartFunctionFieldEquiv Hartshorne.restrictFunctionFieldEquiv_globalToFunctionField Hartshorne.chartFunctionFieldEquiv_symm_globalToFunctionField Hartshorne.exists_coordToRational_eq_of_globalRegular Hartshorne.exists_awayToAtPrime_eq_of_globalRegular Hartshorne.coordinateRingEquivRegularTop_apply Hartshorne.exists_homogeneous_repr_of_globalRegular
---

# Reading a global regular function on a chart

A global regular function on a projective `Y` is a ratio of forms on each chart
that meets `Y`. This is the sentence Hartshorne's proof of
[Theorem 3.4(a)](projective-global-regular.md) opens with, and it comes in two
forms, both proved.

The first is inside the function field: the image of `f` in `K(Y)` lies in the
image of `A(Yᵢ)`, and pushing that through `A(Yᵢ) ≅ S(Y)_(xᵢ)` and
[part (c)](projective-function-field.md) puts the image of `f` in `S(Y)_((0))`
inside the image of `S(Y)_(xᵢ)`. It is a chase along the three isomorphisms
identifying `K(Y)` with the affine chart's function field, checking at each step
that a global regular function stays one. Making the chase possible meant
splitting that identification into named components: a `let`-bound chain of
`RingEquiv`s computes on no element.

The second is pointwise: there are `N` and a form `g` of degree `N` with

`f(P) · xᵢ(P)^N = g(P)` for every `P ∈ Y ∩ Uᵢ`.

## Why both

They say the same thing, and only the second is usable by part (a).

The first mentions `Φᵢ : K(Y) ≅ S(Y)_((0))`, which is built through the chart
`Uᵢ`; readings on different charts are then different terms, and nothing says
they agree. Part (a) has to combine readings from every chart, so that is fatal
there — see the discussion on that node. Pointwise there is nothing to compare.

The pointwise version is also the shorter. Theorem 3.2(a) on the affine chart
says the transported function is a polynomial `p` in the affine coordinates, and
`eval_homogenize` converts that upstairs, the factor `xᵢ^N` being exactly the
discrepancy between evaluating a polynomial and evaluating its homogenisation.

## Depends on

- [Global regular functions inside the function field](../global-regular-in-function-field.md)
- [The charts are isomorphisms of varieties](chart-isomorphism.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](../global-regular-eq-coordinate-ring.md)
- [The function field of a projective variety](projective-function-field.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)
