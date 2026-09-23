---
article_id: af_9ccfa4b4af1188a70942772f
declaration: def
origin: bridged
source_units: [chapter-i-section-6-normalization]
---

# The two separable normalization charts

Fix a separating parameter `t` for the one-dimensional function field `K/k`.
Define

`B₀ = integralClosure(k[t], K)` and
`B∞ = integralClosure(k[t⁻¹], K)`.

Both rings are finite over their polynomial base, finitely generated over
`k`, Dedekind of exact Krull dimension one, and have fraction field `K`.

The pinned Mathlib theorems `IsIntegralClosure.finite` and
`IsIntegralClosure.isDedekindDomain` apply because the separating-parameter
theorem makes both extensions finite separable. No use of the exact
nonseparable Theorems 3.9A or 6.3A is needed. Exact dimension one follows
from invariance under the integral extension of a one-variable polynomial
ring.

Construct the base rings using `Polynomial.algEquivOfTranscendental` to
identify `k[X]` with `k[t]`, identify its fraction field with the intermediate
field `k(t)`, and transport the finite separable extension along that
equivalence. For the second chart, also transport along the proved equality
`k(t⁻¹) = k(t)`. These equivalences and the resulting scalar towers are part of
the packaged chart data, not implicit coercions.

Package the two base subalgebras, their integral closures, and their algebra
maps into one chart datum. Every valuation ring of `K` contains `t` or
`t⁻¹`, so these two normalizations cover all of `C_K`.

## Depends on

- [One-dimensional function fields have separating parameters](separating-parameter.md)
- [Discrete valuation rings of a function field](function-field-dvrs.md)

## Proof depends on

- [Krull dimension is invariant under integral extensions](../affine-varieties/dimension-integral-extension.md)

## Sources

- [Hartshorne I.6, normalization construction in Lemma 6.5 and Corollary 6.6 (pp. 41--42)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
