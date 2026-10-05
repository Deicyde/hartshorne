---
article_id: af_29f475baa591ec20b277f792
declaration: theorem
origin: background
source_units: [chapter-ii-section-8]
statement: formalized
proof: formalized
lean: Hartshorne.kaehlerConormal_rightExact
---

# The conormal exact sequence

Let `B` be an `A`-algebra, let `I ⊆ B`, and put `C = B/I`.  The canonical
sequence

`I/I² → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → 0`

is exact, with the first map carrying the class of `b ∈ I` to `1 ⊗ db`.
No injectivity assertion is made at the left end.

## Depends on

- [The universal module of Kähler differentials](kahler-differential-universal.md)

## Proof depends on

- `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` proves
  exactness at `C ⊗[B] Ω[B⁄A]`.
- `KaehlerDifferential.mapBaseChange_surjective` proves surjectivity onto
  `Ω[C⁄A]`.
- Both primitives are in `Mathlib/RingTheory/Kaehler/Basic.lean`; the full
  source-shaped right-exact sequence is the project wrapper.

## Sources

- [Hartshorne II.8, Proposition 8.4A, printed p. 173](../../../../sources/hartshorne-ii-8.md)
