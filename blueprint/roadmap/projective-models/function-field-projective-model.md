---
article_id: af_78997ddb7372a8a01620fefa
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.exists_nonsingular_projective_model
---

# Nonsingular projective models of function fields

Let `k` be algebraically closed and let `K/k` be a finitely generated field
extension of transcendence degree exactly one.  Then the abstract nonsingular curve `C_K` is isomorphic to a
nonsingular projective curve.  The sole main declaration is planned as
`Hartshorne.ValuationSpace.exists_nonsingular_projective_model`.

This is Theorem 6.9.  No separability assumption is permitted.  The diagonal
map is injective because equal points would give equal DVR subrings.  Every
point of its image closure is hit by choosing a dominating function-field DVR
and applying Lemma 6.4.  A bijection between cofinite curves is a
homeomorphism; the local-ring equality and Exercise 3.3(b) make it an
isomorphism.  Its local DVRs make the projective model nonsingular.

## Depends on

- [Abstract nonsingular curves](../curve-normalization/abstract-nonsingular-curve.md)
- [Curves](../nonsingular-curves/curve.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Intrinsic nonsingularity](../nonsingular-varieties/intrinsic-nonsingularity.md)

## Proof depends on

- [The local ring of an abstract curve](abstract-curve-local-ring.md)
- [Abstract valuation curves have dimension one](abstract-curve-dimension.md)
- [Isomorphisms from topology and local rings](isomorphism-local-criterion.md)
- [The projective diagonal model](projective-diagonal.md)
- [The function field of the diagonal model](projective-model-function-field.md)
- [Local rings of the diagonal model](projective-model-local-rings.md)
- [A dominating function-field DVR](dominating-dvr.md)
- [The local ring determines the point](../nonsingular-curves/local-ring-inclusion-determines-point.md)
- [Quasi-projective curves have the cofinite topology](../curve-normalization/quasiprojective-curve-cofinite.md)

## Sources

- [Hartshorne I.6, Theorem 6.9 (pp. 44--45)](../../sources/hartshorne.md#i6-projective-models)
