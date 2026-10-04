---
article_id: af_7969084b278fd0629e4ab945
declaration: class
origin: bridged
source_units: [chapter-ii-section-5]
mathlib: true
mathlib_declaration: SheafOfModules.IsQuasicoherent
mathlib_file: Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean
---

# Quasi-coherence by local presentations

Define an `𝒪_X`-module to be quasi-coherent in the Mathlib representation when
locally it is the cokernel of a morphism between free module sheaves.  Record
the restriction and gluing calculus for this predicate, including locality on
an open cover.

Hartshorne gives this formulation in Exercise 5.4 as the original definition,
not as a cited or later-used exercise.  This leaf is therefore a representation
bridge: it fixes the implementation predicate but does not yet assert that it
is equivalent to Hartshorne's running local-tilde definition.

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)

## Proof depends on

- Presentations restrict along open immersions.
- Local presentations glue after refining two open covers.

## Sources

- [Hartshorne II.5, quasi-coherence definition on printed p. 111](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
- [Hartshorne II.5, Exercise 5.4 as a representation bridge](../../../sources/hartshorne-ii-5.md#excluded-exercise-clauses)
