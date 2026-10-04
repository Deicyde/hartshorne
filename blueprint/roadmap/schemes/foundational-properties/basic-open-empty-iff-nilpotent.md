---
article_id: af_3cc07813acd961f269cce0e1
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: PrimeSpectrum.basicOpen_eq_bot_iff
mathlib_file: Mathlib/RingTheory/Spectrum/Prime/Topology.lean
---

# An empty principal open detects nilpotence

For `f` in a commutative ring `A`, the principal open `D(f) ⊆ Spec A` is empty
if and only if `f` is nilpotent.

The complement of `D(f)` is `V(f)`.  It is all of `Spec A` exactly when `f`
belongs to every prime ideal, equivalently to the nilradical.  This is Exercise
2.18(a).

## Depends on

- [The Zariski topology on Spec](../spectrum-and-schemes/spec-zero-loci.md)

## Sources

- [Hartshorne II.2, Exercise 2.18(a), used in Proposition 3.1 (pp. 81–82)](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
