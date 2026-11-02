---
article_id: af_5b7e34d5e45271c5c73168b1
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveDegree Hartshorne.projectiveHilbertPolynomial
---

# Hilbert polynomials and degrees of projective algebraic sets

For a projective algebraic set $Y\subseteq\mathbb P^n$, its *Hilbert
polynomial* $P_Y$ is the Hilbert polynomial of the homogeneous coordinate
module $S(Y)=S/J(Y)$. If $P_Y$ has degree $r$, define

$$\deg Y=r!\,\operatorname{lc}(P_Y).$$

The empty set has Hilbert polynomial zero and is assigned degree zero.
For nonempty $Y$, [Hilbert–Serre](hilbert-serre.md) identifies $r$ with
$\dim Y$. The grading is induced by the homogeneous ideal $J(Y)$, and
$Z(\operatorname{Ann}S(Y))=Y$. Integrality and positivity of the degree
are proved in [Hartshorne's Proposition I.7.6(a)](../bezout/hilbert-polynomial-positive-degree.md).

## Depends on

- [The integer grading on a polynomial ring](integer-polynomial-grading.md)
- [Integer-graded submodules and quotients](graded-submodules-and-quotients.md)
- [Hilbert–Serre](hilbert-serre.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Proof depends on

- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Sources

- [Hartshorne I.7, definitions after Theorem 7.5 (p. 52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
