---
article_id: af_7641a33cab715c6d10fcd498
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.hilbertFunction
---

# The Hilbert function

For a finitely generated integer-graded module
$M=\bigoplus_{d\in\mathbb Z}M_d$ over $S=k[x_0,\ldots,x_n]$, its
*Hilbert function* is

$$\varphi_M(d)=\dim_k M_d\qquad(d\in\mathbb Z).$$

Twisting translates its argument:

$$\varphi_{M(l)}(d)=\varphi_M(d+l).$$

A degreewise short exact sequence
$0\to M'\to M\to M''\to0$ gives

$$\varphi_M(d)=\varphi_{M'}(d)+\varphi_{M''}(d).$$

The pieces are finite-dimensional, so this is rank-nullity in each degree.

## Depends on

- [Integer-graded module twists](graded-module-twists.md)
- [Integer-graded submodules and quotients](graded-submodules-and-quotients.md)
- [Finite-dimensional graded pieces](finite-graded-pieces.md)

## Sources

- [Hartshorne I.7, definition of the Hilbert function and exact-sequence identity in Theorem 7.5 (p. 51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
