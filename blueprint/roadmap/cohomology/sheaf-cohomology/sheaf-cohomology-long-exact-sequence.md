---
article_id: af_acc41f7e6e3920d05b1ce349
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
mathlib: true
mathlib_declaration: CategoryTheory.Abelian.Ext.covariantSequence_exact
mathlib_file: Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean
---

# The long exact sequence of sheaf cohomology

Under the Ext model of sheaf cohomology, every short exact sequence of
abelian sheaves gives successive six-term (five-arrow) windows in the cohomology
sequence. These windows are exactly Mathlib's
`Abelian.Ext.covariantSequence`, whose exactness is
`Abelian.Ext.covariantSequence_exact`.

The unique main result is exactness of these windows. Assembly into a single
long exact sequence and naturality belong to the project comparison wrapper
and are not asserted by the `mathlib: true` declaration here.

## Depends on

- [Sheaf cohomology and the Ext model](sheaf-cohomology.md)

## Proof depends on

- [The long exact sequence of right derived functors](../derived-functors/right-derived-long-exact-sequence.md)

## Sources

- [Hartshorne III.2, delegated long exact sequence, printed p. 207](../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)
