---
article_id: af_0e5f5e0fad44547212ec5385
declaration: theorem
origin: background
source_units: [chapter-ii-section-9]
mathlib: true
mathlib_declaration: AdicCompletion.map_exact
mathlib_file: Mathlib/RingTheory/AdicCompletion/Exactness.lean
---

# Exactness of finite-module completion

For a short exact sequence of finite modules over a Noetherian ring, applying
adic completion gives a short exact sequence.

The unique main result is exactness at the completed middle module, exactly
`AdicCompletion.map_exact`; the pinned `map_injective` and `map_surjective`
complete the short-exact package.

## Depends on

- [Adic completion of rings and modules](adic-completion.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.9, Theorem 9.3A(c) (pp.193–194)](../../../../sources/hartshorne-ii-9.md#adic-completion)
- Atiyah–Macdonald, p.108.
- Stacks Project, tags `00MA` and `00MB`.
