---
article_id: af_ab6547f969409d6c33d5d90d
declaration: theorem
origin: cited
source_units: [appendix-c-section-1]
statement: formalized
proof: formalized
lean: Hartshorne.finite_rationalPoints_of_finiteType
---

# A finite-type scheme over a finite field has finitely many rational points

Let `X` be finite type over `F_q`. For every `r>=1`, the set

`X(F_(q^r))=Hom_(Spec F_q)(Spec F_(q^r),X)`

is finite.

## Depends on

- [Morphisms of finite type](../../schemes/first-properties/finite-type.md)
- [Finite-type schemes admit finite affine covers](../../schemes/first-properties/finite-type-finite-affine-cover.md)

## Proof depends on

- Choose a finite affine cover. Each affine piece embeds in finite-dimensional
  affine space over the finite field, whose set of rational points is finite.

## Sources

- [Hartshorne Appendix C.1, definition of `N_r`, p.449](../../../sources/hartshorne-appendix-c-1.md)
