---
declaration: instance
origin: background
source_units: [chapter-ii-section-8]
mathlib: true
mathlib_declaration: KaehlerDifferential.isLocalizedModule_map
mathlib_file: Mathlib/RingTheory/Etale/Kaehler.lean
---

# Localization of Kähler differentials

Let `T` be a localization of an `R`-algebra `S` at a submonoid `M`.  The
canonical map

`Ω[S⁄R] → Ω[T⁄R]`

exhibits the target as the localization of the source at `M`.  Equivalently,
there is a canonical `T`-linear equivalence

`T ⊗[S] Ω[S⁄R] ≃ Ω[T⁄R]`.

The pinned declaration proves this through the formally étale equivalence
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`.

## Depends on

- [The universal module of Kähler differentials](kahler-differential-universal.md)

## Sources

- [Hartshorne II.8, localization clause of background Proposition 8.2A, printed p. 173](../../../../sources/hartshorne-ii-8.md)
