---
article_id: af_7370d04f9ed05fa3fb569f11
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.Projective.exists_mem_locallyQuasiFinite_morphismRestrict Hartshorne.exists_mem_locallyQuasiFinite_morphismRestrict_of_isProper
---

# A finite projective fibre has a quasi-finite neighbourhood

Let $f : Z \to X$ be a projective finite-type morphism of Noetherian schemes.
If the fibre over $P \in X$ is zero-dimensional, then there is an open
neighbourhood $U$ of $P$ such that

$f^{-1}(U) \to U$

is quasi-finite.

More generally, the argument uses neither Noetherian hypothesis, and
projectivity already makes $f$ proper, hence of finite type: for any proper
morphism whose fibre over $P$ has dimension at most zero, the same conclusion
holds.

## Depends on

- [The fibre of a morphism](../../../schemes/fiber-products/scheme-fiber.md)
- [Images of proper schemes](../../../schemes/proper-and-projective/proper-image.md)
- [Morphisms locally of finite type](../../../schemes/first-properties/locally-finite-type.md)

## Proof depends on

- [Projective morphisms are proper](../../../schemes/proper-and-projective/projective-morphism-proper.md)
- Quasi-finiteness is open on the source for a locally finite-type morphism.
  The finite fibre is contained in that open; projectivity makes the image of
  its closed complement closed, so removing that image gives the required
  target neighbourhood.

## Sources

- [Hartshorne V.5, neighbourhood step in Theorem 5.2, p.411](../../../../sources/hartshorne-v-5.md)
