---
declaration: class
origin: bridged
source_units: [chapter-ii-section-5]
mathlib: true
mathlib_declaration: SheafOfModules.IsFinitePresentation
mathlib_file: Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean
---

# Finite type and finite presentation for module sheaves

For a sheaf of modules, distinguish the Mathlib predicates
`SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation`.
Finite type means locally finitely many generators; finite presentation means
locally finitely many generators and relations.  Prove that finite presentation
implies both finite type and quasi-coherence, and preserve these implications
under isomorphism.

This leaf fixes the representation needed later: Hartshorne coherence will be
identified with finite presentation only after imposing locally Noetherian
hypotheses.  It does not make that identification globally.

## Depends on

- [Quasi-coherence by local presentations](quasicoherent-local-presentations.md)

## Proof depends on

- A finite local presentation supplies finite local generators.
- Presentations and their finiteness transport across isomorphisms.

## Sources

- [Hartshorne II.5, coherent-sheaf discussion on printed pp. 111–113](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
