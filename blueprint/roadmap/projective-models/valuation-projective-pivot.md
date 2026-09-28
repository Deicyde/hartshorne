---
article_id: af_d222888a4429ec3f3066f168
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.FunctionFieldDVR.exists_projective_pivot
---

# A projective coordinate pivot

For a nonzero finite family of homogeneous coordinates `f : ι → K` and a
function-field DVR `R`, there is an index `j` whose valuation is minimal, so
every ratio `f i / f j` lies in `R` and the `j`th ratio is one.  The sole main
declaration is
`Hartshorne.FunctionFieldDVR.exists_projective_pivot`.

This packages the coordinate calculation in Proposition 6.8.  It must retain
the nonvanishing conclusion needed to define a projective point after residue
evaluation.

## Depends on

- [Discrete valuation rings of a function field](../curve-normalization/function-field-dvrs.md)
- [Projective space](../projective-varieties/projective-space.md)

## Proof depends on

- [Characterizations of discrete valuation rings](../nonsingular-curves/dvr-characterizations.md)

## Sources

- [Hartshorne I.6, proof of Proposition 6.8 (pp. 43--44)](../../sources/hartshorne.md#i6-projective-models)
