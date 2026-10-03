---
declaration: theorem
origin: bridged
source_units: [chapter-ii-section-5]
---

# Support of a quasi-coherent module

Define the support of `F : X.Modules` by
`Supp(F) = {x | F_x is nonzero}`. If `X = Spec A` and `F = M~`, this set is
`Module.support A M`. Consequently, for finite `M`,
`Supp(M~) = V(ann_A M)`, and the support of a coherent sheaf on a Noetherian
scheme is closed.

This node packages the internal support lemmas needed by the adopted parts of
Exercise 5.6; parts (a)–(c) are not independently adopted targets. The
analogous formula for a single global section,
`Supp(m) = V(ann_A m)`, is a supporting lemma rather than another main
artifact.

## Depends on

- [Stalks of an associated affine module](../modules-and-quasicoherent/tilde-localization.md)
- [Coherent affine-local criterion](../modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [The support of sections and sheaves](../sheaf-functors/support-of-sections-and-sheaves.md)

## Proof depends on

- `Module.mem_support_iff_exists_annihilator`, `Module.support_eq_zeroLocus`,
  and `Module.isClosed_support` from pinned Mathlib.

## Sources

- [Hartshorne II.5, Exercise 5.6(a–c), internal support lemmas (p.124)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
