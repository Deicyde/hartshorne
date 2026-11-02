---
article_id: af_87756b03c53d40cd10c6801e
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso
mathlib_file: Mathlib/Topology/Sheaves/Stalks.lean
---

# Isomorphisms are detected on stalks

For a morphism $\varphi : F \longrightarrow G$ of sheaves on $X$, $\varphi$ is an isomorphism if and
only if every induced map $F_{x} \longrightarrow G_{x}$ is an isomorphism.

Stalkwise injectivity gives equality of sections locally. Stalkwise
surjectivity gives local preimages, which agree on overlaps by
injectivity and therefore glue by the sheaf axiom.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)
- [Stalks and germs](stalks-and-germs.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, Proposition 1.1 (p. 63)](../../../sources/hartshorne-ii-1.md#stalks-germs-and-morphisms-printed-pp-6263)
