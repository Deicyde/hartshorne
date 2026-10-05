---
article_id: af_95d1a2e01824862c840b8993
declaration: def
origin: cited
source_units: [chapter-ii-section-9]
statement: formalized
proof: formalized
lean: Hartshorne.InverseSystem.IsMittagLeffler Hartshorne.InverseSystem.isMittagLeffler_of_surjective Hartshorne.InverseSystem.isMittagLeffler_of_isArtinian
---

# Inverse systems and the Mittag–Leffler condition

For a sequence of abelian groups `A n` with compatible transition maps from
larger indices to smaller ones, define its inverse limit, morphisms and exact
sequences of systems, and the Mittag–Leffler condition: for every `n`, the
images in `A n` eventually stabilize.

Use natural-number indexing throughout. When the system comes from an ideal,
term `n` will mean reduction modulo `I^(n+1)`.

The unique main artifact is the sequential specialization of Mathlib's
`CategoryTheory.Functor.IsMittagLeffler`. Surjective transition maps imply ML,
and termwise descending-chain conditions imply ML; these are supporting lemmas
rather than separate roadmap nodes. The pinned cofiltered-system API supplies
the general set-valued predicate, but not Hartshorne's later exactness theorem
for abelian-group systems.

## Depends on

No project-local mathematical result beyond Mathlib's categorical limits and
abelian groups. The representation should reuse
`Mathlib/CategoryTheory/CofilteredSystem.lean` rather than define an unrelated
ML predicate.

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.9, definitions (pp.190–192) and Examples 9.1.1–9.1.2 (p.192)](../../../../sources/hartshorne-ii-9.md#inverse-systems-and-sheaf-limits)
- Stacks Project, tags `0595` and `0596`.
