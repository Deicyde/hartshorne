---
article_id: af_a79b80aca295435c1fad8a9f
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.moduleFinite_integralClosure_of_finiteType Hartshorne.finiteType_integralClosure_of_finiteType
---

# Finiteness of integral closure

Let $A$ be a finitely generated algebra domain over the algebraically closed
field $k$, let $K$ be its fraction field, and let $L/K$ be a finite algebraic
extension.  If $A'$ is the integral closure of $A$ in $L$, then $A'$ is a
finite $A$-module and therefore a finitely generated $k$-algebra.

This is Theorem 3.9A under the standing hypothesis on $k$, with no
separability assumption on $L/K$. Choose a finite injective Noether
normalization $P = k[X_1,\ldots,X_n] \to A$. Localizing this finite map makes
$\operatorname{Frac}(A)/\operatorname{Frac}(P)$ finite-dimensional; combining it with the given finite
extension $L/\operatorname{Frac}(A)$ makes $L/\operatorname{Frac}(P)$ finite-dimensional by the tower law.
The integral elements of $L$ over $A$ and over $P$ coincide. Finiteness of the
normalization over $P$ therefore gives a finite $P$-spanning family, and the
same family spans over the larger ring $A$.


## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Normalizations of polynomial rings are finite](polynomial-normalization-finite.md)

## Sources

- [Hartshorne I.3, Theorem 3.9A (p. 20)](../../sources/hartshorne.md#i3)
- [Project-authored proof specification for Theorem I.3.9A](../../sources/hartshorne.md#project-authored-proof-specification-for-theorem-i39a)
