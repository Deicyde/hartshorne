---
article_id: af_f81e55ec00ccd41a8d8ad98b
declaration: theorem
origin: cited
source_units: [appendix-a-section-3]
---

# Chern classes are natural under pullback

Let `f:X'->X` be a morphism of nonsingular quasi-projective varieties and
let `E` be locally free on `X`.  Then

`c_i(f^*E)=f^*c_i(E)`

for every `i`, equivalently `c_t(f^*E)=f^*c_t(E)`.

## Depends on

- [Chern classes from the projective-bundle relation](chern-classes-projective-bundle-definition.md)
- [Functorial pullback on Chow rings](../chow/product/pullback-ring-functoriality.md)

## Proof depends on

- Base change identifies `P(f^*E)` with `X' times_X P(E)` and carries the
  tautological quotient bundle, hence `xi`, to its pullback.  Uniqueness of
  the projective-bundle coefficients gives the formula.

## Sources

- [Hartshorne Appendix A §3, C2, p.430](../../../sources/hartshorne-appendix-a-3.md)
