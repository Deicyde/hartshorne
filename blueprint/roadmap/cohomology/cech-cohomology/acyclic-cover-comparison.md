---
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-1-4]
not_ready: true
---

# Leray's acyclic-cover comparison

Let `U` cover a topological space `X`, and let `F` be an abelian sheaf.
Assume that for every nonempty finite intersection `V` of members of `U`,

`H^q(V,F|_V)=0` for every `q>0`.

Then every Čech comparison map is an isomorphism
`CechH^p(U,F) ≅ H^p(X,F)`.

## Depends on

- [Comparison from Čech to sheaf cohomology](cech-derived-comparison.md)

## Proof depends on

- [The sheafified Čech resolution](sheafified-cech-resolution.md)
- [Comparison by acyclic resolutions](../derived-functors/acyclic-resolution-comparison.md)
- Resolve `F` injectively and form the first-quadrant double complex whose
  `(p,q)` term is the product of sections of the `q`th injective over all
  `(p+1)`-fold intersections.
- In the Čech direction, flasqueness contracts the positive rows; in the
  resolution direction, the finite-intersection hypothesis kills positive
  vertical cohomology, leaving the ordinary Čech complex on the bottom row.
- Adopt a complete proof source or a project proof of convergence and of the
  exactness properties of the products used by the two total-complex
  filtrations.

## Sources

- [Hartshorne III, Exercise 4.11 (p.225)](../../../sources/hartshorne-iii-3-4.md#cech-construction-and-comparison)
- [External proof obligations](../../../sources/hartshorne-iii-3-4.md#external-proof-obligations)
