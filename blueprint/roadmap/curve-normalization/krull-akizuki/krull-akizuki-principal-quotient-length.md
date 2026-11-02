---
article_id: af_e7855d30b528371d2b2b6b45
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.krullAkizuki_principalQuotient_isFiniteLength
---

# Principal quotients of finite-rank modules have finite length

Let $A$ be a one-dimensional Noetherian domain with fraction field $K$, let
$r\in\mathbb N$, and let $M$ be an $A$-submodule of $K^r$. For every nonzero $a\in A$,
the quotient

$M / aM$

has finite length as an $A$-module.

This is Stacks Project, Tag 00PF, isolated as the module-theoretic core of the
Krull--Akizuki proof. The element $a$ lies in only finitely many primes, all
maximal, and the Artinian ring $A/(a)$ decomposes as the product of its
localizations at those primes. The same decomposition applies to $M/aM$.
At each maximal ideal $\mathfrak{m}$, apply the local finite-length lemma to the
$A_{\mathfrak m}$-submodule $M_{\mathfrak m}\subseteq K^r$; summing the finitely many localized lengths gives
the global finite-length conclusion. This is the proof of Tag 00PF and does
not require $M$ itself to be finitely generated or to have full rank $r$.


## Depends on

No project-local statement prerequisites.

## Sources

- [Hartshorne I.6, Theorem 6.3A and its cited algebraic input (p. 40)](../../../sources/hartshorne.md#i6-integral-closure-theorem)
- [Stacks Project, the local finite-length lemma (Tag 00PE)](https://stacks.math.columbia.edu/tag/00PE)
- [Stacks Project, finite length of $M/aM$ (Tag 00PF)](https://stacks.math.columbia.edu/tag/00PF)
