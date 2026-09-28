---
article_id: af_53c37b8474739d7a3ebebb55
declaration: def
origin: bridged
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.abstractNonsingularCurveLocalRingAlgEquiv
---

# The local ring of an abstract curve

For an abstract nonsingular open curve `X ⊆ C_K` and `R ∈ X`, the local
ring at `R` is canonically isomorphic, as a local `k`-algebra embedded in `K`,
to the valuation ring represented by `R`.  The sole main declaration is
`Hartshorne.ValuationSpace.abstractNonsingularCurveLocalRingAlgEquiv`.

The compatibility with the two maps into `K` is part of the conclusion.  It
must not be weakened to an abstract ring equivalence.  Regularity of this DVR
also supplies the nonsingularity instance used in Theorem 6.9 as a supporting
consequence of the same implementation leaf.

## Depends on

- [Abstract nonsingular curves](../curve-normalization/abstract-nonsingular-curve.md)
- [Discrete valuation rings of a function field](../curve-normalization/function-field-dvrs.md)
- [The local ring at a point](../morphisms/local-ring.md)

## Proof depends on

- [Regularity near a valuation](regular-near-valuation.md)
- [The function field of an abstract nonsingular curve](../curve-normalization/valuation-space-function-field.md)
- [Residue fields of function-field DVRs](../curve-normalization/valuation-residue-field.md)

## Sources

- [Hartshorne I.6, definition of an abstract nonsingular curve (p. 42) and proof of Theorem 6.9 (p. 45)](../../sources/hartshorne.md#i6-projective-models)
