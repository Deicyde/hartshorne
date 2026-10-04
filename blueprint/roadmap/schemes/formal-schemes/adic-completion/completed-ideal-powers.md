---
article_id: af_793552093819c4b5f36ad12d
declaration: theorem
origin: bridged
source_units: [chapter-ii-section-9]
---

# Completed ideals and their powers

Let `A` be Noetherian, let `I` be an ideal, and write `Ahat` for its adic
completion. The inverse limit

`Ihat = lim_n I / I^(n+1)`

embeds as an ideal of `Ahat` and is canonically equal to `I Ahat`. More
generally, for every positive `r`, completion identifies the module
`I^r` with `I^r Ahat`; consequently

`Ihat / I^(n+1) Ahat ≅ I / I^(n+1)`.

This project bridge packages the ideal/module identifications needed by
Hartshorne beyond the pinned theorem that completed powers are kernels of
evaluation.

## Depends on

- [Adic completion of rings and modules](adic-completion.md)

## Proof depends on

- [Powers in an adic completion](adic-completion-powers.md)
- [Finite-module completion as tensor product](finite-module-completion-tensor.md)
- [Quotients of an adic completion](adic-completion-quotients.md)

## Sources

- [Hartshorne II.9, Theorem 9.3A(a,b) (pp.193–194)](../../../../sources/hartshorne-ii-9.md#adic-completion)
- Stacks Project, tags `05GG`, `031C`, and `00MA`.
