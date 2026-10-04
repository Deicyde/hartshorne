---
article_id: af_d15239e64c87122975f4ca4a
declaration: def
origin: background
source_units: [chapter-ii-section-8]
mathlib: true
mathlib_declaration: KaehlerDifferential.tensorKaehlerEquiv
mathlib_file: Mathlib/RingTheory/Kaehler/TensorProduct.lean
---

# Base change for Kähler differentials

Given a pushout square of rings with `B = S ⊗[R] A`, there is a canonical
`B`-linear equivalence

`B ⊗[A] Ω[A⁄R] ≃ Ω[B⁄S]`.

This is the base-change clause of Hartshorne's background Proposition 8.2A in
Mathlib's pushout-oriented API.  Localization is recorded separately because
its exact stable declaration uses the formally étale localization API.

## Depends on

- [The universal module of Kähler differentials](kahler-differential-universal.md)

## Sources

- [Hartshorne II.8, Proposition 8.2A, printed p. 173](../../../../sources/hartshorne-ii-8.md)
