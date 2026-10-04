---
article_id: af_d0bf12084f8433d9aaa2bb0e
declaration: definition
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Pullback of divisors along finite curve morphisms

For a finite morphism `f : X → Y` of nonsingular curves, define its degree as
`[K(X):K(Y)]`. Since the ground field is algebraically closed, define the
degree of a curve divisor `D = sum_i n_i P_i` by
`deg D = sum_i n_i`. For a closed point `Q : Y` and a local parameter `t` at
`Q`, define

`f*Q = sum_(P in X, f(P)=Q) ord_P(t) P`

and extend additively to `f* : Div Y → Div X`. Prove independence of the
choice of `t`, finiteness of the fibre sum, and
`f*((g)) = (f# g)`, so pullback descends to `Cl Y → Cl X`.

The direction is part of the type: divisors on the target pull back to
divisors on the source. No divisor pushforward is introduced here.

## Depends on

- [Codimension-one stalks are DVRs](../weil-divisors/codimension-one-stalk-dvr.md)
- [Principal divisors have finite support](../weil-divisors/principal-divisor-finite-support.md)
- [Finite morphisms](../../first-properties/finite-morphism.md)
- [The function field is functorial for dominant morphisms](../../../morphisms/function-field-functorial.md)

## Proof depends on

- A finite morphism has finite fibres.
- A unit in `O_{Y,Q}` maps to a unit in every `O_{X,P}` above `Q`.

## Sources

- [Hartshorne II.6, curve-divisor degree and finite-curve pullback definitions on printed pp.137–138](../../../../sources/hartshorne-ii-6.md#divisors-on-curves)
