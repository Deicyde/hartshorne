---
article_id: af_a80104f765e1ab68f0ef60db
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.krullAkizuki_quotientIdeal_isFiniteLength Hartshorne.krullAkizuki_quotientIdeal_moduleFinite
---

# Finite-length quotients in Krull--Akizuki

Let $A$ be a one-dimensional Noetherian domain with fraction field $K$, let
$L/K$ be finite, and let $B$ be an intermediate $A$-subalgebra of $L$. For
every nonzero ideal $I$ of $B$, the quotient $B/I$ has finite length as an
$A$-module. In particular, it is a finite $A$-module.

This is the ideal-quotient step in the Krull--Akizuki theorem. By Stacks
Project, Tag 0H7L, every nonzero ideal $I$ of $B$ meets $A$ nontrivially. Choose
$0 \ne a \in I \cap A$, a $K$-basis $L\cong K^n$, and view the image of $B$ as an
$A$-submodule of $K^n$. Transport $B/aB$ across this equivalence and apply the
preceding principal-quotient theorem; the quotient map $B/aB \to B/I$ then gives
finite length for $B/I$. The result must apply to an arbitrary intermediate
ring $B$; assuming that $B$ is already finite or integral over $A$ would make
the later Krull--Akizuki step circular.


## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Principal quotients of finite-rank modules have finite length](krull-akizuki-principal-quotient-length.md)

## Sources

- [Hartshorne I.6, Theorem 6.3A and its cited algebraic input (p. 40)](../../../sources/hartshorne.md#i6-integral-closure-theorem)
- [Stacks Project, nonzero ideals meet the base (Tag 0H7L)](https://stacks.math.columbia.edu/tag/0H7L)
- [Stacks Project, Krull–Akizuki (Tag 00PG)](https://stacks.math.columbia.edu/tag/00PG)
