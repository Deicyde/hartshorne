---
article_id: af_1f814f85ea1d9f30e9756c16
declaration: def
origin: cited
source_units: [appendix-a-section-3]
---

# Chern classes from the projective-bundle relation

Let `E` be locally free of positive rank `r` on a nonsingular quasi-projective variety
`X`.  In Hartshorne's quotient convention, let `pi:P(E)->X` and put
`xi=[O_(P(E))(1)] in A^1(P(E))`, using `A^1(P(E))~=Pic(P(E))`. Define the classes

`c_i(E) in A^i(X)`, `0<=i<=r`,

by `c_0(E)=1` and the relation

`sum_(i=0)^r (-1)^i pi^*c_i(E) xi^(r-i)=0`

in `A^r(P(E))`.  The Chow projective-bundle formula gives existence and
uniqueness of the coefficients.  Define

`c_t(E)=sum_(i=0)^r c_i(E)t^i`.

The later line-bundle axiom proves `xi=c_1(O(1))`; that equality is not used
circularly in this definition.

## Depends on

- [The Chow projective-bundle formula](../chow/properties/chow-projective-bundle-formula.md)
- [The codimension-one Chow group is the Picard group](../chow/properties/chow-codimension-one-picard.md)
- [Projective bundles](../../schemes/projective-geometry/relative-proj-bundles/projective-bundle.md)

## Sources

- [Hartshorne Appendix A §3, Chern-class definition, p.429](../../../sources/hartshorne-appendix-a-3.md)
