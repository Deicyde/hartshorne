---
article_id: af_ab6547f969409d6c33d5d90d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.finite_rationalPoints_of_finiteType
---

# A finite-type scheme over a finite field has finitely many rational points

Let $X$ be finite type over $\mathbb{F}_q$. For every $r\ge 1$, the set

$X(\mathbb{F}_{q^r})=\operatorname{Hom} _{(\operatorname{Spec} \mathbb{F}_q)}(\operatorname{Spec} \mathbb{F}_{q^r},X)$

is finite.

## Depends on

- [Morphisms of finite type](../../schemes/first-properties/finite-type.md)
- [Finite-type schemes admit finite affine covers](../../schemes/first-properties/finite-type-finite-affine-cover.md)

## Proof depends on

- Choose a finite affine cover. Each affine piece embeds in finite-dimensional
  affine space over the finite field, whose set of rational points is finite.

## Sources

- [Hartshorne Appendix C.1, definition of $N_r$, p.449](../../../sources/hartshorne-appendix-c-1.md)
