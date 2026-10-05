---
article_id: af_01b3b42bdfcfbcdd30757572
declaration: theorem
origin: background
source_units: [chapter-ii-section-8]
statement: formalized
proof: formalized
lean: Hartshorne.kaehlerFirstExactSequence
---

# The first exact sequence

For ring maps `A → B → C`, the natural sequence of `C`-modules

`C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`

is exact.  The first map sends `c ⊗ db` to `c · db`, and the second forgets
that elements of `B` may vary over `A`.

## Depends on

- [The universal module of Kähler differentials](kahler-differential-universal.md)

## Proof depends on

- `KaehlerDifferential.exact_mapBaseChange_map` proves exactness at
  `Ω[C⁄A]`.
- `KaehlerDifferential.map_surjective` proves surjectivity onto `Ω[C⁄B]`.
- Both primitives are in `Mathlib/RingTheory/Kaehler/Basic.lean`; the full
  source-shaped right-exact sequence is the project wrapper.

## Sources

- [Hartshorne II.8, Proposition 8.3A, printed p. 173](../../../../sources/hartshorne-ii-8.md)
