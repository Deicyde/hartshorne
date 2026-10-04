---
article_id: af_086741f04b12f875a3c34599
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Sheaf.isLocallySurjective_iff_epi
mathlib_file: Mathlib/Topology/Sheaves/LocallySurjective.lean
---

# Epimorphisms are locally surjective

A morphism of sheaves of abelian groups is epic if and only if every section
of the target lifts after passing to an open cover. Equivalently, every induced
map on stalks is surjective. This is the form used in the proof of Proposition
5.6 on printed p. 113.

Pinned Mathlib gives the cover formulation as
`TopCat.Presheaf.isLocallySurjective_iff`, its equivalence with stalkwise
surjectivity as `locally_surjective_iff_surjective_on_stalks`, and the epi
characterization as the main declaration above.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)
- [Stalks and germs](stalks-and-germs.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, Caution 1.2.1 and Exercise 1.3(a), used on p. 113](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
