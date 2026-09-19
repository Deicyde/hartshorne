---
article_id: af_8a05003a5be1e12ca9cc7683
declaration: def
origin: cited
source_units: [chapter-i-section-4]
---

# The graph hypersurface has localized coordinate ring

For `0 ≠ f ∈ k[x₁,…,x_n]`, let
`H_f = Z(t f - 1) ⊆ 𝔸ⁿ⁺¹`. Its coordinate ring has a canonical
`k`-algebra equivalence

`A(H_f) ≃ₐ[k] k[x₁,…,x_n]_f`.

This equivalence is the main result. Geometrically, the next node identifies
`H_f` with the principal open `D(f)`.

## Proof plan

Use `MvPolynomial.optionEquivLeft` (or `finSuccEquiv`) to view the extra
variable as the localization inverse. Mathlib's
`IsLocalization.Away.mvPolynomialQuotientEquiv` first identifies the raw
quotient by `(t f - 1)` with the away localization. Then
`Localization.Away.isDomain` and `Ideal.Quotient.isDomain_iff_prime` show that
the principal ideal is prime, the Nullstellensatz identifies it with the
vanishing ideal of `H_f`, and `Ideal.quotientEquivAlg` transports the raw
quotient equivalence to `A(H_f)`.

## Depends on

- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [Algebraic sets and radical ideals](../affine-varieties/radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.4, Lemma 4.2 (p. 25)](../../sources/hartshorne.md#i4)
