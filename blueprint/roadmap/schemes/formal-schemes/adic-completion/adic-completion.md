---
article_id: af_8c189989ca7f6150d723a7af
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AdicCompletion
mathlib_file: Mathlib/RingTheory/AdicCompletion/Basic.lean
---

# Adic completion of rings and modules

For an ideal $I$ of a commutative ring $A$ and an $A$-module $M$, define

$\widehat{M}=\varprojlim_n M/I^{n+1}M$.

For $M=A$, the completion $\widehat A$ has its induced
commutative-ring structure and canonical homomorphism
$A\to\widehat A$. With this indexing, term zero is reduction
modulo $I$.

## Depends on

- [Inverse systems and the Mittag–Leffler condition](../inverse-systems/inverse-system-mittag-leffler.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.9, completion definitions (p.193)](../../../../sources/hartshorne-ii-9.md#adic-completion)
