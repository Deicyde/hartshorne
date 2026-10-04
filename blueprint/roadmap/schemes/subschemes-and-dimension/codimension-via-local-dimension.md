---
article_id: af_44b83243fe293608bea01657
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Codimension as an infimum of local dimensions

Let `X` be an integral scheme of finite type over a field, and let `Y ⊆ X` be
a nonempty closed subset. Then

`codim(Y,X) = inf { ringKrullDim 𝒪_{X,P} | P ∈ Y }`.

For each `P`, identify the dimension of the stalk with the coheight of `P`.
The closure of `P` is an irreducible closed subset of `Y`, while the generic
point of every irreducible closed subset of `Y` supplies the reverse
inequality between the two infima.

## Depends on

- [Codimension in a scheme](scheme-codimension.md)
- [Integral schemes](../first-properties/integral-scheme.md)
- [Morphisms of finite type](../first-properties/finite-type.md)

## Proof depends on

- `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` and the generic-point
  correspondence for irreducible closed subsets.

## Sources

- [Hartshorne II.3, Exercise 3.20(c) (pp. 94–95)](../../../sources/hartshorne-ii-3.md#later-used-exercises)
