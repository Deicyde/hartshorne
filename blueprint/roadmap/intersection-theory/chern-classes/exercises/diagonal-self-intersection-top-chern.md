---
declaration: theorem
origin: cited
source_units: [appendix-a-exercises]
---

# The diagonal self-intersection is the top tangent Chern class

Let `X` be a nonsingular projective variety of dimension `n`, and let
`Delta:X->X times X` be its diagonal.  Under the natural identification of
`X` with its diagonal,

`Delta^* Delta_*(1_X)=c_n(T_X) in A^n(X)`.

Equivalently, the self-intersection class `Delta^2` is the top Chern class of
the tangent bundle, because

`N_(Delta/(X times X)) ~= T_X`.

## Depends on

- [The regular-embedding self-intersection formula](../regular-embedding-self-intersection.md)
- [The tangent-normal exact sequence](../../../schemes/differentials/canonical-bertini/tangent-normal-exact-sequence.md)
- [Diagonal reduction of intersections](../../chow/product/diagonal-reduction.md)

## Proof depends on

- Identify the conormal bundle of the diagonal with `Omega_X` using the two
  projections; dualizing identifies the normal bundle with `T_X`.  Apply C7.

## Sources

- [Hartshorne Appendix A, Exercise A.6.6, p.437](../../../../sources/hartshorne-appendix-a-3.md)
