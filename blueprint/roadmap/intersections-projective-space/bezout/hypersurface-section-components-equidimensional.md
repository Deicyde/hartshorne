---
article_id: af_9580fea2449e7376bca1ba58
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
---

# Proper hypersurface sections are equidimensional

Assume `n > 0`. Let `Y ⊆ ℙⁿ` be a projective variety of natural dimension
`r > 0`, and let `H = Z(f)` for an irreducible homogeneous polynomial `f` of
positive degree. If `Y` is not contained in `H`, then every irreducible
component `Z` of `Y ∩ H` has

`projDim (projectiveComponentCarrier Z) = r - 1`.

The main declaration is planned as
`Hartshorne.projectiveHypersurfaceSectionComponent_projDim_eq`. The projective
dimension theorem gives the lower bound `r-1`. The component carrier is a
proper closed subset of the irreducible variety `Y`, so strict dimension drop
gives the matching upper bound. This is the equidimensionality assertion used
when Theorem 7.7 replaces top-dimensional minimal primes by the geometric
components of the section.

## Depends on

- [The projective dimension theorem for components](../dimension/projective-dimension-theorem.md)
- [Projective intersection components on an affine chart](../dimension/projective-intersection-components.md)
- [A degree-d hypersurface has degree d](hypersurface-hilbert-polynomial.md)

## Proof depends on

- [Projective codimension one is a hypersurface](../dimension/projective-codimension-one-hypersurface.md)
- [Projective varieties of complementary dimension meet](../dimension/projective-intersection-nonempty.md)

## Sources

- [Hartshorne I.7, proof of Theorem 7.7 using Theorem 7.2 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
