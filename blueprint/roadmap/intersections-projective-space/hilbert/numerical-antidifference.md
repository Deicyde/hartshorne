---
article_id: af_ca2bfce28489b72dde40649c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_isNumericalPolynomial_eventuallyEq_of_diff
---

# Discrete antidifferentiation of a numerical polynomial

Let $f:\mathbb Z\to\mathbb Z$. Suppose that a numerical polynomial
$Q\in\mathbb Q[z]$ satisfies

$$f(n+1)-f(n)=Q(n)$$

for all sufficiently large $n$. Then there is a numerical polynomial $P$
with $f(n)=P(n)$ for all sufficiently large $n$.

Expand $Q$ in the integral binomial basis and raise each basis index by one.
Pascal's identity gives a polynomial whose forward difference is $Q$.
The remaining difference from $f$ is eventually constant and is absorbed
into the constant coefficient. When $Q\ne0$, antidifferentiation raises
the degree by one and divides its leading coefficient by the new degree.

## Depends on

- [Numerical polynomials](numerical-polynomial.md)

## Proof depends on

- [Numerical polynomials have integral binomial expansions](numerical-binomial-expansion.md)

## Sources

- [Hartshorne I.7, Proposition 7.3(b) (p. 50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
