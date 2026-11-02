---
article_id: af_47ddc8c1c5ad90500da8b0d7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.gradedPrimeFiltration_annihilator_le_iff
---

# Minimal primes in a graded prime filtration

Fix a graded prime filtration of $M$ with factor primes
$\mathfrak p_1,\ldots,\mathfrak p_t$. For every prime ideal $\mathfrak p$,

$$\operatorname{Ann}M\subseteq\mathfrak p
\quad\Longleftrightarrow\quad
\mathfrak p_i\subseteq\mathfrak p\text{ for some }i.$$

The prime $\mathfrak p$ need not be homogeneous. The minimal factor primes
are exactly the primes minimal over $\operatorname{Ann}M$.

For each filtration step, the quotient factor has annihilator
$\mathfrak p_i$, and the product of that ideal with the annihilator of the
preceding term annihilates the next term. Primality gives the required
disjunction. Induction on the finite filtration proves the equivalence.

## Depends on

- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)
- [Graded prime filtrations](graded-prime-filtration.md)

## Sources

- [Hartshorne I.7, Proposition 7.4(a) (p. 50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
