---
declaration: def
origin: cited
source_units: [chapter-ii-section-8]
mathlib: true
mathlib_declaration: KaehlerDifferential.linearMapEquivDerivation
mathlib_file: Mathlib/RingTheory/Kaehler/Basic.lean
---

# The universal module of Kähler differentials

For a ring map `A → B`, the canonical derivation

`d : B → Ω[B⁄A]`

is universal: for every `B`-module `M`, composition with `d` gives a natural
linear equivalence

`Hom_B(Ω[B⁄A], M) ≃ Der_A(B,M)`.

Mathlib constructs `Ω[B⁄A]` as the cotangent module `I/I²` for the kernel `I`
of multiplication `B ⊗[A] B → B`.  Hartshorne's Proposition 8.1A is the
background diagonal model supporting the universal construction; it is not a
second project definition of differentials.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne II.8, definitions on p. 172 and background Proposition 8.1A on p. 173](../../../../sources/hartshorne-ii-8.md)
