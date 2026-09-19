---
article_id: af_99905fcdb2a616c538f5d376
declaration: theorem
origin: cited
source_units: [chapter-i-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.graphProjection_isIso
---

# The complement of a hypersurface is affine

Let `0 ≠ f ∈ k[x₁,…,x_n]`, let `Y = Z(f)`, and write
`D(f) = 𝔸ⁿ − Y`. Then `D(f)` is isomorphic to the graph hypersurface

`H_f = Z(x_{n+1} f − 1) ⊆ 𝔸ⁿ⁺¹`.

In particular `D(f)` has an affine presentation (Lemma 4.2). The nonzero
hypothesis is essential in the project's irreducible, nonempty notion of a
variety: for `f = 0`, the complement is empty.

## The proof

Projection `π : H_f → 𝔸ⁿ`, `(a₁,…,a_{n+1}) ↦ (a₁,…,a_n)`, lands in `D(f)` and
is a morphism because its coordinates are regular. It is inverse on points to

`(a₁,…,a_n) ↦ (a₁,…,a_n, 1/f(a₁,…,a_n))`, whose last coordinate is a regular
function on `D(f)` because `f` is nowhere zero there. The criterion for maps to
affine varieties therefore makes this inverse a morphism. The graph
hypersurface is an affine variety because its coordinate algebra is the
localization at `f`, hence a domain; that algebra calculation is split into
[its own node](principal-open-coordinate-ring.md).

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Morphisms](../morphisms/morphism.md)
- [The graph hypersurface has localized coordinate ring](principal-open-coordinate-ring.md)

## Proof depends on

- [Criterion for a morphism to an affine variety](../morphisms/morphism-to-affine-criterion.md)

## Sources

- [Hartshorne I.4, Lemma 4.2 (p. 25)](../../sources/hartshorne.md#i4)
