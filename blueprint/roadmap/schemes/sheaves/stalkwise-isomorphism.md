---
article_id: af_87756b03c53d40cd10c6801e
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso
mathlib_file: Mathlib/Topology/Sheaves/Stalks.lean
---

# Isomorphisms are detected on stalks

For a morphism `φ : F ⟶ G` of sheaves on `X`, `φ` is an isomorphism if and
only if every induced map `Fₓ ⟶ Gₓ` is an isomorphism.

This is exactly `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` in the pinned
Mathlib. Its proof follows Hartshorne: stalkwise injectivity gives equality of
sections locally, while stalkwise surjectivity supplies compatible local
preimages which the sheaf axiom glues.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)
- [Stalks and germs](stalks-and-germs.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, Proposition 1.1 (p. 63)](../../../sources/hartshorne-ii-1.md#stalks-germs-and-morphisms-printed-pp-6263)
