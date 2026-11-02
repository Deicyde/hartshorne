---
article_id: af_7969084b278fd0629e4ab945
declaration: class
origin: bridged
mathlib: true
mathlib_declaration: SheafOfModules.IsQuasicoherent
mathlib_file: Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean
---

# Quasi-coherence by local presentations

A sheaf of $\mathcal{O}_X$-modules has local presentations when
locally it is the cokernel of a morphism between free module sheaves.
This property is preserved by restriction and can be checked on an
open cover.

Hartshorne's Exercise II.5.4 gives this formulation of quasi-coherence.
The equivalence with the local affine tilde description is proved
in [the affine-local criterion](quasicoherent-affine-local-criterion.md).

## Depends on

- [Sheaves of modules](sheaves-of-modules.md)

## Proof depends on

- Presentations restrict along open immersions.
- Local presentations glue after refining two open covers.

## Sources

- [Hartshorne II.5, quasi-coherence definition on printed p. 111](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
- [Hartshorne II.5, Exercise 5.4 as a representation bridge](../../../sources/hartshorne-ii-5.md#excluded-exercise-clauses)
