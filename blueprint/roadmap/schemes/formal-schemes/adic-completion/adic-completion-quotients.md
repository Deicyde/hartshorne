---
article_id: af_2c04f4445787c66b36bedc16
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.exists_adicCompletionQuotientRingEquiv
---

# Quotients of an adic completion

Let $A$ be Noetherian and $I$ an ideal. For every natural number $n$, reduction
induces a ring isomorphism

$\widehat{A} / I^{n+1} \widehat{A} \cong A / I^{n+1}$.

The quotient isomorphism follows from surjectivity of reduction
and the description of its kernel.

## Depends on

- [Adic completion of rings and modules](adic-completion.md)

## Proof depends on

- [Powers in an adic completion](adic-completion-powers.md)
- The reduction map from the completion is surjective.
- The first isomorphism theorem for commutative rings.

## Sources

- [Hartshorne II.9, Theorem 9.3A(a) (pp.193–194)](../../../../sources/hartshorne-ii-9.md#adic-completion)
- Atiyah–Macdonald, p.109.
- Stacks Project, tags $05GG$ and $031C$.
