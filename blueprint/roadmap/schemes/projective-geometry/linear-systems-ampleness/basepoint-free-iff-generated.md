---
article_id: af_b93fb27e7e0a0c6cbb1f4340
declaration: theorem
origin: cited
lean: Hartshorne.LinearSystem.IsBasePointFree Hartshorne.LinearSystem.isBasePoint_iff_forall_germ_mem Hartshorne.LinearSystem.forall_mem_support_iff_forall_germ_mem Hartshorne.LinearSystem.isBasePointFree_iff_isGeneratedBySections Hartshorne.LinearSystem.isBasePointFree_iff_isGeneratedBySections_of_span_eq Hartshorne.LinearSystem.existsUnique_morphism_of_isBasePointFree Hartshorne.LinearSystem.morphism Hartshorne.LinearSystem.morphism_spec Hartshorne.LinearSystem.isBasePointFree_ofFamily_pullback Hartshorne.LinearSystem.isClosedImmersion_iff_of_span_eq Hartshorne.LinearSystem.isClosedImmersion_morphism_iff
statement: formalized
proof: formalized
---

# Base-point-freeness and global generation

A point is a base point of the linear system represented by $V$ exactly when
every section in $V$ vanishes in its fibre. Consequently the system is
base-point-free exactly when $V$ generates the associated invertible sheaf.
It follows that a base-point-free linear system determines a morphism to projective space
(Remark 7.8.1), and Proposition 7.3 can be restated in terms of linear systems
(Remark 7.8.2).

## Depends on

- [Linear systems](linear-system-api.md)
- [Morphisms from generated invertible sheaves](morphism-from-generated-line-bundle.md)
- [Separation of points and tangent vectors](separates-points-tangents-iff-closed-immersion.md)

## Sources

- [Hartshorne II.7, Lemma 7.8 and Remarks 7.8.1–7.8.2 (p.158)](../../../../sources/hartshorne-ii-7.md#morphisms-ampleness-and-linear-systems)
