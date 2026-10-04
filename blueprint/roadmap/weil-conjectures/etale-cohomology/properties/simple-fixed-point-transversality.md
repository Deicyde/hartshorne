---
article_id: af_6dde09ee9211b4d76f7e8c8b
declaration: theorem
origin: bridged
source_units: [appendix-c-section-3]
---

# The tangent criterion for a simple fixed point

Let `X` be smooth and `f:X->X`.  At a fixed closed point `x`, the graph of
`f` meets the diagonal transversally exactly when

`1-df_x:T_xX->T_xX`

is invertible.  In that case the scheme-theoretic fixed point is reduced and
has local intersection multiplicity one.

Isolation without this tangent condition does not imply multiplicity one.

## Depends on

- [The Zariski tangent map](../../../cohomology/smooth-morphisms/zariski-tangent-map.md)
- [Intersection-product existence](../../../intersection-theory/chow/product/intersection-product-existence.md)
- [Proper intersections expand with local multiplicities](../../../intersection-theory/chow/product/proper-intersection-local-expansion.md)
- [Serre's Tor intersection multiplicity](../../../intersection-theory/chow/product/serre-tor-intersection-multiplicity.md)

## Proof depends on

- Identify the tangent map of `(id,f):X->X times X` modulo the diagonal with
  `1-df_x`; invertibility makes graph and diagonal complementary regular
  embeddings and gives local length one.

## Sources

- [Hartshorne Appendix C §3, multiplicity-one condition in property 3.5, p.453](../../../../sources/hartshorne-appendix-c-3.md#properties-31-through-35-printed-p453)
