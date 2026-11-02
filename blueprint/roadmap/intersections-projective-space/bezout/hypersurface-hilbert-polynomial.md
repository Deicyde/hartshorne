---
article_id: af_cfa44c986c3be95861967648
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.hypersurface_hilbertPolynomial_and_degree
---

# A degree-d hypersurface has degree d

Assume $n > 0$. Let $f \in k[x_{0},\ldots ,x_{n}]$ be an irreducible homogeneous
polynomial of positive degree $d$, and let $H = Z(f) \subseteq \mathbb{P} ^{n}$. Then

$P_H(z)=P_{\mathbb P^n}(z)-P_{\mathbb P^n}(z-d)$

and $\deg H = d$.

This is Proposition 7.6(d). Multiplication by $f$ gives the graded exact
sequence $0 \to S(-d) \to S \to S/(f) \to 0$; the Hilbert-function difference gives
the polynomial identity, and the leading term is $d/(n-1)!$. Irreducibility
is essential: it identifies the homogeneous vanishing ideal of $Z(f)$ with
$(f)$; without it, replacing $f$ by a power would leave the zero set unchanged
while changing $d$. The positive ambient dimension excludes the degenerate
case $Z(x_{0}) = \varnothing$ in $\mathbb{P} ^{0}$, whose projective degree is zero.

## Depends on

- [Integer-graded module twists](../hilbert/graded-module-twists.md)
- [The Hilbert function](../hilbert/hilbert-function.md)
- [Projective space has degree one](projective-space-hilbert-polynomial.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)

## Proof depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Sources

- [Hartshorne I.7, Proposition 7.6(d) (p. 52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
