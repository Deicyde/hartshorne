---
article_id: af_c9b34d562bca7bd9350f8d51
declaration: definition
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.integerHomogeneousSubmodule
---

# The integer grading on a polynomial ring

For $S=k[x_0,\ldots,x_n]$, extend the total-degree grading to integer
indices by setting $S_d=0$ when $d<0$. For $d\geq0$, the piece $S_d$
is the usual space of homogeneous polynomials of total degree $d$.

An ideal is homogeneous for this integer grading exactly when it is
homogeneous for the nonnegative grading. This allows the twist convention
$M(l)_d=M_{d+l}$ to be used uniformly for all integers $d,l$.

## Depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)

## Sources

- [Hartshorne I.7, graded-ring and graded-module conventions before Proposition 7.4 (p. 50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
