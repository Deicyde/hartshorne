---
declaration: theorem
origin: cited
source_units: [appendix-a-sections-4-5]
---

# Proper pushforward on K0

For a proper morphism `f:X->Y`, define

`f_!([F])=sum_i (-1)^i [R^i f_*F]`

on coherent-sheaf K0. This is additive in short exact sequences and therefore
descends to a group homomorphism. It is not ordinary sheaf pushforward.

## Depends on

- [Vector-bundle and coherent-sheaf K0 on a smooth variety](smooth-k0-vector-bundle-coherent-comparison.md)
- [Coherence of projective higher direct images](../../../cohomology/higher-direct-images/projective-higher-direct-images-coherent.md)
- [The long exact sequence of right derived functors](../../../cohomology/derived-functors/right-derived-long-exact-sequence.md)
- [Quasi-projective morphisms](../../../schemes/proper-and-projective/quasi-projective-morphism.md)
- [Projective iff proper and very ample](../../../schemes/projective-sheaves/projective-iff-proper-very-ample.md)

## Proof depends on

- A proper morphism between the quasi-projective varieties in Appendix A is
  projective via its graph and a relative very ample sheaf, so projective
  coherent-direct-image finiteness applies.
- The long exact sequence of higher direct images makes the alternating K0
  sum additive on short exact sequences.

## Sources

- [Hartshorne Appendix A, proper K-theory pushforward, p.436](../../../../sources/hartshorne-appendix-a-4-5.md#ktheory-and-generalized-riemannroch-printed-pp435436)
