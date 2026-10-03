---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Genus-two curves are canonically hyperelliptic

Let `X` be a Chapter IV curve of genus two. Its canonical linear system has
degree two and projective dimension one, has no base points, and determines a
finite morphism

`X -> P^1_k`

of degree two. Consequently every genus-two curve is hyperelliptic.

## Depends on

- [The degree of a canonical divisor](canonical-divisor-degree.md)
- [The Riemann–Roch theorem](riemann-roch.md)
- [Base-point-freeness and global generation](../../schemes/projective-geometry/linear-systems-ampleness/basepoint-free-iff-generated.md)
- [Morphisms from generated invertible sheaves](../../schemes/projective-geometry/linear-systems-ampleness/morphism-from-generated-line-bundle.md)
- [Nonconstant maps of complete curves are finite](../../schemes/divisors/curve-divisors/nonconstant-complete-curve-map-finite.md)

## Proof depends on

- `l(K)=g=2`; if a point were a base point, comparison of `l(K-P)` with
  Riemann–Roch gives a contradiction.
- The morphism has pullback `O(1)` equal to `O_X(K)`, so its degree is
  `deg K=2`.

## Sources

- [Hartshorne IV.1, Exercise 1.7(a), p.298](../../../sources/hartshorne-iv-1.md#exercise-disposition-printed-pp297298)
