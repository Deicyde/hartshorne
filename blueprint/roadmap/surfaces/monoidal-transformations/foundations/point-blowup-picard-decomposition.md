---
article_id: af_bddc667ee73c34544588f951
declaration: isomorphism
origin: cited
source_units: [chapter-v-section-3]
---

# The Picard group of a point blowup

For `pi:X_tilde->X`, pullback and the exceptional class induce an isomorphism

`Pic(X) direct-sum Z ~= Pic(X_tilde)`,

`(L,n) |-> pi^*L tensor O_X_tilde(nE)`.

Thus every divisor class on `X_tilde` has a unique expression
`pi^*D+nE`.

## Depends on

- [The blown-up surface is smooth and projective](point-blowup-smooth-projective-surface.md)
- [The exceptional curve has self-intersection minus one](exceptional-curve-self-intersection.md)
- [Restriction of class groups to open complements](../../../schemes/divisors/weil-divisors/class-group-open-restriction.md)
- [Divisor classes and the Picard group](../../../schemes/divisors/cartier-picard/divisor-class-picard-equivalence.md)

## Proof depends on

- Restriction identifies the complements `X_tilde-E` and `X-P`; their class
  groups are `Cl(X)/0` and `Cl(X_tilde)/Z[E]`.
- Pullback splits the resulting exact sequence, and `E^2=-1` makes the
  exceptional-class map injective.

## Sources

- [Hartshorne V.3, Proposition 3.2, pp.386–387](../../../../sources/hartshorne-v-3.md)
