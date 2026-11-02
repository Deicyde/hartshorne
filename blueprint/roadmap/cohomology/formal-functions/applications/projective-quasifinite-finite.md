---
article_id: af_a3d45df32cfc447043223c78
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Projective.isFinite_of_finite_fibres Hartshorne.Projective.isFinite_of_finite_preimage_singleton
---

# Projective quasi-finite morphisms are finite

Let $f : X \to Y$ be a projective morphism of Noetherian schemes. If every
fibre of $f$ is finite, equivalently if $f$ is quasi-finite, then $f$ is a
finite morphism.

This is the projective case of the theorem that a proper locally
quasi-finite morphism is finite. Hartshorne uses the exercise in
V.1.10 and V.5.2.

Both Noetherian hypotheses are retained in the source-case theorem to match
Hartshorne's setting. Properness itself supplies local finite type and
quasi-compactness, so finite point-preimages imply local quasi-finiteness
without either Noetherian hypothesis; the separately named general theorem
therefore applies to arbitrary schemes.

## Depends on

- [Projective morphisms are proper](../../../schemes/proper-and-projective/projective-morphism-proper.md)
- [Finite morphisms](../../../schemes/first-properties/finite-morphism.md)

## Proof depends on

- A proper locally quasi-finite morphism is finite.
- For a finite-type morphism, finite scheme-theoretic fibres are equivalent
  to local quasi-finiteness.

## Sources

- [Hartshorne III.11, Exercise 11.2, p.280](../../../../sources/hartshorne-iii-11-12.md#exercise-11-disposition-pp280281)
