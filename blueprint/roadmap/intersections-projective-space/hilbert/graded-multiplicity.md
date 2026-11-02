---
article_id: af_4b49ee4a3033d8c3e5250ee9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.gradedPrimeFiltration_multiplicity_eq_count
---

# Multiplicity in a graded prime filtration

For a prime $\mathfrak p$ minimal over $\operatorname{Ann}M$, define

$$\mu_{\mathfrak p}(M)=\operatorname{length}_{S_{\mathfrak p}}M_{\mathfrak p}.$$

For every graded prime filtration of $M$, this length is finite and equals
the number of factors whose prime is $\mathfrak p$.

After localization at $\mathfrak p$, a factor with prime $\mathfrak p_i$
vanishes unless $\mathfrak p_i\subseteq\mathfrak p$. Minimality turns
this containment into equality. Each surviving factor is the residue field
of $S_{\mathfrak p}$ and has length one. Additivity of length therefore
counts the factors and shows that the number is independent of the
chosen filtration.

## Depends on

- [Graded prime filtrations](graded-prime-filtration.md)
- [Minimal primes in a graded prime filtration](prime-filtration-support.md)

## Sources

- [Hartshorne I.7, multiplicity definition and Proposition 7.4(b) (p. 51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
