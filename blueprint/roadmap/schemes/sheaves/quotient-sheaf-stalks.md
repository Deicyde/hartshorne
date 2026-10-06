---
article_id: af_c9b09b7dfb1cbf3560551fe4
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.abelianQuotientSheaf_stalkAddEquiv_exists
---

# Stalks of quotient sheaves

If `F'` is a subsheaf of a sheaf of abelian groups `F`, define `F/F'` by
sheafifying the presheaf `U ↦ F(U)/F'(U)`. For every point `x`, the canonical
map induces an additive equivalence

`(F/F')ₓ ≃+ Fₓ/F'ₓ`.

The same construction identifies the cokernel of a sheaf morphism with the
sheafification of its pointwise cokernel. The source-facing stalk equivalence
should be exported even though it follows abstractly from exactness of the
stalk functor.

## Depends on

- [Stalks and germs](stalks-and-germs.md)
- [The associated sheaf](associated-sheaf.md)

## Proof depends on

- [Exactness is detected on stalks](stalkwise-exactness.md)
- [Sheafification preserves stalks](associated-sheaf-stalks.md)

## Sources

- [Hartshorne II.1, quotient and cokernel sheaves (p. 65)](../../../sources/hartshorne-ii-1.md#kernels-images-quotients-and-exactness-printed-pp-6365)
