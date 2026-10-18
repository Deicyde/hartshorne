---
article_id: af_a3d45df32cfc447043223c78
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
statement: formalized
proof: formalized
lean: Hartshorne.Projective.isFinite_of_finite_fibres Hartshorne.Projective.isFinite_of_finite_preimage_singleton
---

# Projective quasi-finite morphisms are finite

Let `f : X -> Y` be a projective morphism of Noetherian schemes. If every
fibre of `f` is finite, equivalently if `f` is quasi-finite, then `f` is a
finite morphism.

This later-used exercise is a projective specialization of the modern theorem
that a proper locally quasi-finite morphism is finite. That stronger modern
result is proof infrastructure; this source-shaped wrapper is not marked as
an exact Mathlib result. The exercise is used in Hartshorne V.1.10 and V.5.2.

Both Noetherian hypotheses are retained in the source-case theorem to match
Hartshorne's setting. Properness itself supplies local finite type and
quasi-compactness, so finite point-preimages imply local quasi-finiteness
without either Noetherian hypothesis; the separately named general theorem
therefore applies to arbitrary schemes.

## Depends on

- [Projective morphisms are proper](../../../schemes/proper-and-projective/projective-morphism-proper.md)
- [Finite morphisms](../../../schemes/first-properties/finite-morphism.md)

## Proof depends on

- `IsFinite.of_isProper_of_locallyQuasiFinite` in pinned Mathlib.
- For a finite-type morphism, finite scheme-theoretic fibres are equivalent
  to local quasi-finiteness.

## Sources

- [Hartshorne III.11, Exercise 11.2, p.280](../../../../sources/hartshorne-iii-11-12.md#exercise-11-disposition-pp280281)
