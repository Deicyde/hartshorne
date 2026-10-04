---
article_id: af_476ce91f67dd82c20e6495bd
declaration: theorem
origin: cited
source_units: [chapter-iii-section-5]
---

# Euler characteristic is additive

For a coherent sheaf `F` on a projective scheme over a field `k`, define

`χ(F)=Σ_i (-1)^i dim_k Hⁱ(X,F)`.

This is a finite sum. Every short exact sequence
`0→F'→F→F''→0` satisfies `χ(F)=χ(F')+χ(F'')`.

## Depends on

- [Coherent projective cohomology is finite](../projective-cohomology/projective-coherent-cohomology-finite.md)
- [Grothendieck vanishing](../sheaf-cohomology/grothendieck-vanishing/grothendieck-vanishing.md)

## Proof depends on

- [The long exact sequence of sheaf cohomology](../sheaf-cohomology/sheaf-cohomology-long-exact-sequence.md)
- Alternating dimension in a finite exact sequence of finite-dimensional
  vector spaces.
- `Module.sum_neg_one_pow_finrank_eq_zero_of_exact` is exact generic Mathlib
  prior art; the coherent-sheaf Euler characteristic remains project-specific.

## Sources

- [Hartshorne III, Exercise 5.1, p.230](../../../sources/hartshorne-iii-5.md#adopted-exercises-pp230233)
