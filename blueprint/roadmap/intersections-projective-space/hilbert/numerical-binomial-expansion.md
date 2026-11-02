---
article_id: af_8f4533c12c01e96df3437796
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isNumericalPolynomial_iff_exists_binomialExpansion
---

# Numerical polynomials have integral binomial expansions

A polynomial $P\in\mathbb Q[z]$ is numerical if and only if it has a
finite expansion

$$P(z)=\sum_{r\geq0}c_r\binom zr,\qquad c_r\in\mathbb Z.$$

Consequently $P(n)$ is integral for every integer $n$, not merely for
sufficiently large integers. This is Hartshorne's Proposition I.7.3(a).
If $P$ has degree $r$, its top coefficient satisfies

$$r!\,\operatorname{lc}(P)=c_r.$$

The proof is induction on degree. Forward difference sends the degree-$r$
binomial polynomial to the degree-$(r-1)$ one. Induction gives integrality
of all nonconstant coefficients, and one sufficiently large integral
evaluation gives integrality of the constant coefficient.

## Depends on

- [Numerical polynomials](numerical-polynomial.md)

## Sources

- [Hartshorne I.7, Proposition 7.3(a) (pp. 49–50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
