---
article_id: af_7d5b5dcb8f543a104d25695b
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# Hironaka's normality lemma

Let `A` be a local Noetherian domain essentially of finite type over a field,
and let `t : A`. Assume that `tA` has a unique minimal associated prime `p`,
that `t` generates the maximal ideal of `A_p`, and that `A/p` is normal. Then
`p=tA` and `A` is normal.

## Depends on

- Local Noetherian domains, associated primes, localization, and normal rings.

## Proof depends on

- [Serre's normality criterion](../../../schemes/differentials/local-complete-intersections/serre-normality-criterion.md):
  a normal local domain of dimension at least two has depth at least two.
- [Finite normalization over a field](../../../schemes/normalization-and-exercises/normalization-finite-type-field.md).
- Quotient by a regular element lowers depth, so the maximal ideal is not an
  associated prime of the quotient of the normalization by `t`.
- A finite birational algebra over a normal domain is equal to that domain.
- Nakayama's lemma applied to `Abar=A+t Abar`.

## Sources

- [Hartshorne III.9, Lemma 9.12, pp.264–265](../../../../sources/hartshorne-iii-9.md#normal-families-and-hironakas-lemma-pp263265)
- Hironaka [1], as cited by Hartshorne.
