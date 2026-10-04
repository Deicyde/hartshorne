---
article_id: af_12230dca41ee47c4aefe7488
declaration: definition
origin: cited
source_units: [chapter-iii-sections-1-4]
---

# The ordered Čech complex

For a well-ordered open cover `U = (U_i)` and an abelian sheaf `F`, define
the cochain complex

`C^p(U,F) = product_(i_0 < ... < i_p) F(U_i0 ∩ ... ∩ U_ip)`

with the alternating restriction differential. Define
`CechH^p(U,F)` as its `p`th cohomology.

## Depends on

- [Complexes in an abelian category](../derived-functors/abelian-complexes-and-homotopy.md)
- [Intersections of open sets](../../schemes/sheaves/sheaves-of-abelian-groups.md)

## Proof depends on

- The alternating-face identity gives `d^2=0`.
- `CategoryTheory.cechComplexFunctor` in
  `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean` is partial prior
  art: a normalization comparison is required because it retains all tuples.

## Sources

- [Hartshorne III.4, definition and Remark 4.0.1 (pp.218–219)](../../../sources/hartshorne-iii-3-4.md#cech-construction-and-comparison)
- [Čech representation choice](../../../sources/hartshorne-iii-3-4.md#project-authored-representation-choices)

