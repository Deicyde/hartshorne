---
article_id: af_e2c74229d0e5f0d585bda655
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.mem_valuationSubring_iff_exists_regular_neighborhood
---

# Regularity near a valuation

Let `K/k` be a one-dimensional function field, `R : FunctionFieldDVR k K`,
and `q : K`.  Then `q ∈ R` if and only if there is an open neighbourhood
`U` of `R` in `C_K` on which `q` is a regular function.  The sole main
declaration is
`Hartshorne.ValuationSpace.mem_valuationSubring_iff_exists_regular_neighborhood`.

This exposes the local fact used in Proposition 6.8: nonnegative valuation is
exactly regularity near the missing point.  Its implementation publicizes and
generalizes the private `regularDomain`, `regularValue`, and
`rationalRepOfElement` machinery rather than duplicating it.

## Depends on

- [Discrete valuation rings of a function field](../curve-normalization/function-field-dvrs.md)
- [Regular functions on the valuation space](../curve-normalization/valuation-regular-functions.md)

## Proof depends on

- [A rational function has finitely many poles](../curve-normalization/finite-poles.md)
- [The valuation-space regularity axioms](../curve-normalization/valuation-regular-functions-local.md)

## Sources

- [Hartshorne I.6, discussion on p. 42 and Proposition 6.8 (pp. 43--44)](../../sources/hartshorne.md#i6-projective-models)
