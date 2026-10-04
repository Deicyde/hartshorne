---
article_id: af_12b14eba4b45f85ba3eb4dca
declaration: theorem
origin: background
source_units: [chapter-ii-section-9]
---

# Noetherianity of adic completion

If `A` is Noetherian and `I` is an ideal, then the adic completion `Ahat` is a
Noetherian ring.

Pinned Mathlib has no general `IsNoetherianRing (AdicCompletion I A)` instance,
so this remains a project theorem rather than an upstream alias.

## Depends on

- [Adic completion of rings and modules](adic-completion.md)

## Proof depends on

- [Quotients of an adic completion](adic-completion-quotients.md)
- Finite generation of `I` and Noetherianity of the associated graded ring,
  or the standard quotient of a formal power-series ring proof.

## Sources

- [Hartshorne II.9, Theorem 9.3A(d) (pp.193–194)](../../../../sources/hartshorne-ii-9.md#adic-completion)
- Atiyah–Macdonald, p.113.
- Stacks Project, tag `0316`.
- Pending Mathlib PR
  [`#38331`](https://github.com/leanprover-community/mathlib4/pull/38331)
  proves this result but is not present in the pinned checkout.
