---
article_id: af_a20c7a4e46cf50484916c16c
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# The Picard group of a projective bundle

Let `Y` be an integral finite-type scheme over an algebraically closed field
and let `E` be finite locally free of constant rank at least two. Pullback and
tensor powers of the tautological sheaf induce an isomorphism

`Pic(Y) times Z ~= Pic(P(E))`,

`(N,n) |-> pi^* N tensor O_P(E)(n)`.

Unlike the earlier [II.7 projective-bundle Picard node](../../../schemes/projective-geometry/relative-proj-bundles/projective-bundle-picard.md),
this exercise removes the regularity hypothesis by using cohomology and base
change over an integral finite-type base.

## Depends on

- [Fibrewise-isomorphic line bundles descend from the base](fiberwise-isomorphic-line-bundles-descend.md)
- [Projective bundles](../../../schemes/projective-geometry/relative-proj-bundles/projective-bundle.md)
- [The tautological quotient on a projective bundle](../../../schemes/projective-geometry/relative-proj-bundles/projective-bundle-tautological-quotient.md)
- [The Picard group of projective space](../../../schemes/divisors/cartier-picard/projective-space-picard-group.md)

## Proof depends on

- Restrict to every projective-space fibre to obtain the locally constant
  degree, twist it to degree zero, and descend the remaining line bundle.

## Sources

- [Hartshorne III, Exercise 12.5, p.291](../../../../sources/hartshorne-iii-11-12.md#exercise-12-disposition-pp291292)
