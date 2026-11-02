---
article_id: af_793552093819c4b5f36ad12d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.completedIdealPowers
---

# Completed ideals and their powers

Let $A$ be Noetherian, let $I$ be an ideal, and write $\widehat{A}$ for its adic
completion. The inverse limit

$\widehat{I} = \lim _n I / I^{n+1}$

embeds as an ideal of $\widehat{A}$ and is canonically equal to $I \widehat{A}$. More
generally, for every positive $r$, completion identifies the module
$I^r$ with $I^r \widehat{A}$; consequently

$\widehat{I} / I^{n+1} \widehat{A} \cong I / I^{n+1}$.

These identifications connect completed ideals, their module
structures, and the kernels of reduction maps.

## Depends on

- [Adic completion of rings and modules](adic-completion.md)

## Proof depends on

- [Powers in an adic completion](adic-completion-powers.md)
- [Finite-module completion as tensor product](finite-module-completion-tensor.md)
- [Quotients of an adic completion](adic-completion-quotients.md)

## Sources

- [Hartshorne II.9, Theorem 9.3A(a,b) (pp.193–194)](../../../../sources/hartshorne-ii-9.md#adic-completion)
- Stacks Project, tags $05GG$, $031C$, and $00MA$.
