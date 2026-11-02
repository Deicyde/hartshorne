---
article_id: af_db1104282c693bcd83a273b9
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projZeroSet Hartshorne.IsProjAlgebraicSet Hartshorne.IsHomogeneousSet
---

# Projective algebraic sets

A homogeneous $f \in S$ of degree $d$ satisfies $f(\lambda a) = \lambda ^{d} f(a)$, so whether
$f$ vanishes at a point of $\mathbb{P} ^{n}$ is well defined even though $f$ is not a
function on $\mathbb{P} ^{n}$. For a set $T$ of homogeneous elements put
$Z(T)=\{P\in\mathbb P^n:f(P)=0\text{ for all }f\in T\}$, and for a homogeneous ideal $\mathfrak{a}$
put $Z(\mathfrak{a} ) = Z(T)$ with $T$ the homogeneous elements of $\mathfrak{a}$. A subset of $\mathbb{P} ^{n}$ is
an *algebraic set* when it is such a $Z(T)$.

Proposition 2.1 records the closure properties: finite unions and arbitrary
intersections of algebraic sets are algebraic, and $\varnothing$ and $\mathbb{P} ^{n}$ are algebraic.
Hartshorne leaves the proof to the reader as it copies Proposition 1.1.

Since $S$ is Noetherian, every $Z(T)$ is $Z(f_{1},\ldots ,f_r)$ for finitely many
homogeneous $f_{i}$; that reduction is used whenever a hypersurface argument needs
a single equation.

## Depends on

- [Projective space](projective-space.md)
- [Homogeneous ideals](homogeneous-ideal.md)

## Sources

- [Hartshorne I.2, zero sets of homogeneous elements and Proposition 2.1 (p. 9)](../../sources/hartshorne.md#i2)
