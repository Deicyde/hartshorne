---
article_id: af_c6af33de69690ddc1dd4ade6
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.existsUnique_hilbertPolynomial_primeQuotient
---

# Hilbert polynomials of shifted prime quotients

Let $\mathfrak p$ be a homogeneous prime ideal of
$S=k[x_0,\ldots,x_n]$ and let $l\in\mathbb Z$. There is a unique
numerical polynomial $P\in\mathbb Q[z]$ which agrees, for all sufficiently
large integer $d$, with the Hilbert function of $(S/\mathfrak p)(l)$.
If $Z(\mathfrak p)$ is empty, then $P=0$. If
$\dim Z(\mathfrak p)=r$, then $P$ is nonzero of degree $r$ and has
positive leading coefficient.

Apply [Hilbert–Serre](hilbert-serre.md) to the shifted prime quotient.
Twisting preserves its annihilator and translates the polynomial's
argument, so it changes neither degree nor leading coefficient. In the
nonempty case, eventual nonnegativity of the Hilbert function gives a
positive leading coefficient.

## Depends on

- [Hilbert–Serre](hilbert-serre.md)
- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)
- [The integer grading on a polynomial ring](integer-polynomial-grading.md)
- [Integer-graded module twists](graded-module-twists.md)
- [The Hilbert function](hilbert-function.md)

## Proof depends on

- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Sources

- [Hartshorne I.7, prime-quotient induction in the proof of Theorem 7.5 (p. 51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
