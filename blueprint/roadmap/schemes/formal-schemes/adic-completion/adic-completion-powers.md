---
article_id: af_cbdf227317053eb5051629df
declaration: theorem
origin: background
source_units: [chapter-ii-section-9]
mathlib: true
mathlib_declaration: AdicCompletion.pow_smul_top_eq_ker_eval
mathlib_file: Mathlib/RingTheory/AdicCompletion/Completeness.lean
---

# Powers in an adic completion

If `I` is finitely generated, then for every `n`, multiplication by the ideal
power on the completed module is exactly the kernel of reduction:

`I^(n+1) • top = ker (AdicCompletion.eval I M (n+1))`.

For `M = A`, this identifies the completed power with
`I^(n+1) Ahat`. The kernel equality is the unique main result and is exactly
the pinned declaration named in the metadata.

## Depends on

- [Adic completion of rings and modules](adic-completion.md)

## Proof depends on

- Finite generation of powers of a finitely generated ideal.

## Sources

- [Hartshorne II.9, Theorem 9.3A(a) (pp.193–194)](../../../../sources/hartshorne-ii-9.md#adic-completion)
- Stacks Project, tags `05GG` and `031C`.
