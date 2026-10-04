---
article_id: af_427839755df16337bb053fa0
declaration: theorem
origin: cited
source_units: [chapter-iv-section-4]
---

# Classification of complex multiplication orders

Let `X(C)=C/(Z+Z*tau)`. If `End(X,P0)` is larger than `Z`, then `tau` belongs
to an imaginary quadratic field and the endomorphism ring is an order in the
ring of integers of that field.

Conversely, write `tau=r+s*sqrt(-d)` with `r,s in Q`, `d>0`. Then `X` has
complex multiplication and

`End(X,P0) = {a+b*tau | a,b in Z, 2*b*r in Z,
                         b*(r^2+d*s^2) in Z}`.

## Depends on

- [Endomorphisms as lattice multipliers](endomorphisms-as-lattice-multipliers.md)

## Proof depends on

- Writing `alpha=a+b*tau` and `alpha*tau=c+e*tau` gives quadratic equations
  for both `tau` and `alpha`; the latter shows every endomorphism is integral
  over `Z`.

## Sources

- [Hartshorne IV.4, Theorem 4.19, pp.330–331](../../../../sources/hartshorne-iv-4.md)
