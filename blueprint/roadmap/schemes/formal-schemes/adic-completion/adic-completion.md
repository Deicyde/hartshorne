---
declaration: def
origin: cited
source_units: [chapter-ii-section-9]
mathlib: true
mathlib_declaration: AdicCompletion
mathlib_file: Mathlib/RingTheory/AdicCompletion/Basic.lean
---

# Adic completion of rings and modules

For an ideal `I` of a commutative ring `A` and an `A`-module `M`, define

`Mhat = lim_n M / I^(n+1) M`.

For `M = A`, equip `Ahat` with its induced commutative-ring structure and the
canonical map `A ⟶ Ahat`. Stage zero is reduction modulo `I`, not modulo
`I^0`; the shift by one reconciles Hartshorne's positive indices with
Mathlib's natural-number-indexed `AdicCompletion`.

Pinned Mathlib's `AdicCompletion I M` is exactly the compatible-family model
of this inverse limit.

## Depends on

- [Inverse systems and the Mittag–Leffler condition](../inverse-systems/inverse-system-mittag-leffler.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.9, completion definitions (p.193)](../../../../sources/hartshorne-ii-9.md#adic-completion)
