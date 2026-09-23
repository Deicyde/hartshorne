---
article_id: af_e31d8787e86350185ec8ff60
declaration: def
origin: cited
source_units: [chapter-i-section-6-abstract-curves]
---

# Abstract nonsingular curves

Let `K/k` be a one-dimensional function field.  An abstract nonsingular curve
is a nonempty open subset `U` of the cofinite valuation space `C_K`, equipped
with the induced topology and with regular functions

`𝒪(U') = ⋂_{R ∈ U'} R`

on its open subsets, read as `k`-valued functions by residue evaluation.

Package each such `U` as a `Hartshorne.Variety k`.  A nonempty open subset of
an infinite cofinite space is irreducible, and the preceding regularity theorem
supplies restriction, closed zero loci, division, and locality.  Keep the
ambient function field `K` in the definition so the comparison map in
Proposition 6.7 is canonical.

Although the carrier `U` is nonempty, its lattice of open subsets includes
`∅`. Use the explicit empty-open convention from the regular-function article
there; only nonempty opens use injectivity of residue evaluation.

This representation uses the project's deliberately abstract `Variety`
structure.  It does not assert in advance that `U` is quasi-projective;
Proposition 6.7 proves that for the open subsets arising from nonsingular
quasi-projective curves.

## Depends on

- [The cofinite valuation space](valuation-space-topology.md)
- [Regular functions on the valuation space](valuation-regular-functions.md)

## Proof depends on

- [The valuation-space regularity axioms](valuation-regular-functions-local.md)

## Sources

- [Hartshorne I.6, definition of an abstract nonsingular curve (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
