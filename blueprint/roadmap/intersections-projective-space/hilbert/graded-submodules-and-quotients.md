---
article_id: af_00d868cf7f23d86aaa14cd83
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.gradedSubquotient_exact
---

# Integer-graded submodules and quotients

Let $M=\bigoplus_{d\in\mathbb Z}M_d$ be an integer-graded $S$-module
and let $N\subseteq M$ be a homogeneous submodule. Intersections with
$M_d$ grade $N$, and the images of $M_d$ grade $M/N$. In every degree,

$$0\longrightarrow N_d\longrightarrow M_d\longrightarrow(M/N)_d
\longrightarrow0$$

is exact. The same construction grades $N_2/N_1$ when
$N_1\subseteq N_2\subseteq M$ are homogeneous submodules.

Homogeneity ensures that the quotient decomposition is well defined.
Exactness follows by taking homogeneous components of the ordinary
submodule and quotient maps.

## Depends on

- [Integer-graded module twists](graded-module-twists.md)

## Proof depends on

- [The integer grading on a polynomial ring](integer-polynomial-grading.md)

## Sources

- [Hartshorne I.7, graded subquotients in Proposition 7.4 and Theorem 7.5 (pp. 50–51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
