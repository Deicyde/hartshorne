---
article_id: af_dc1508fedff9a089a2641a04
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-normalization]
---

# A rational function has finitely many poles

Let `K/k` be a one-dimensional function field and let `x : K`.  Then

`{R ∈ C_K | x ∉ R}`

is finite.  This is Lemma 6.5.

Choose a separating parameter `t` and the two finite Dedekind normalizations
of `k[t]` and `k[t⁻¹]`. Every valuation ring contains `t` or `t⁻¹`, so
these two charts cover `C_K`. On either chart, write `x = a/b` in the fraction
field of the normalization. If `x` does not belong to the localization at a
center `℘`, then `b ∈ ℘`. Distinct DVRs have distinct centers, and only
finitely many maximal ideals contain the nonzero principal ideal `(b)`, by
finite factorization of ideals in a Dedekind domain. Taking the union of the
two finite exceptional sets proves the result.

The proof also establishes the companion statement used in Proposition 6.7:
for `0 ≠ x : K`, only finitely many `R ∈ C_K` have `x ∈ 𝔪_R`.
Expose both statements from the same implementation, with finiteness of poles
as the headline result.

## Depends on

- [Discrete valuation rings of a function field](function-field-dvrs.md)

## Proof depends on

- [The two separable normalization charts](separable-normalization-charts.md)
- [A DVR containing a Dedekind subring is its localization](dedekind-subring-localization.md)

## Sources

- [Hartshorne I.6, Lemma 6.5 (p. 41)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
