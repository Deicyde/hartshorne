---
article_id: af_b501809e0faea306655db32d
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
---

# Bézout for reducible plane curves without a common component

Let `Y,Z ⊆ ℙ²` be projective algebraic sets with
`projDim Y = projDim Z = 1`, every irreducible component carrier of either set
of projective dimension one, and no common component in the carrier-equality
sense stated in the pointwise-multiplicity article. Then `Y ∩ Z` is finite and

`∑ P ∈ (Y ∩ Z).toFinset,`
`  (reduciblePlaneCurveIntersectionMultiplicity Y Z P : ℚ)`
`= projectiveDegree Y * projectiveDegree Z`,

where `toFinset` uses the finiteness theorem from the pointwise-multiplicity
article. The unique main declaration is planned as
`Hartshorne.reducible_plane_curve_bezout`.

This formalizes the pure/equidimensional interpretation of Remark 7.8.2.
Expand the pointwise sum into the finite triple sum, apply the irreducible
plane-curve theorem to each component pair (which is distinct by the
no-common-component hypothesis), and factor the resulting finite sums using
the two component-degree identities.

## Depends on

- [Pointwise multiplicity for reducible plane curves](reducible-plane-curve-pointwise-multiplicity.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)

## Proof depends on

- [Degree of a pure projective curve is the sum of component degrees](pure-projective-curve-degree-components.md)
- [Bézout's theorem for distinct plane curves](plane-curve-bezout.md)

## Sources

- [Hartshorne I.7, Remark 7.8.2 (p. 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
