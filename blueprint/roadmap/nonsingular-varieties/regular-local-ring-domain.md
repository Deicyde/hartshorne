---
article_id: af_86df2fc5bb33de30c3e39629
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.RegularLocal.isDomain Hartshorne.RegularLocal.isDomain_of_spanFinrank_eq Hartshorne.RegularLocal.isRegularLocalRing_quotient_of_notMem_sq Hartshorne.RegularLocal.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes Hartshorne.RegularLocal.isDomain_of_isPrime_bot
---

# A regular local ring is an integral domain

Let $(A, \mathfrak m)$ be a regular local ring. Then $A$ is an integral
domain.

Hartshorne uses this commutative-algebra fact, without proving it, in the
proof of Theorem II.8.8: to show that a regular local ring $B$ has free
differentials, he passes to the quotient field of $B$, which exists only
because $B$ is a domain.

The proof is by induction on $d=\dim_\kappa(\mathfrak m/\mathfrak m^2)$, where
$\kappa = A/\mathfrak m$. If $d=0$, then $\mathfrak m=0$ by Nakayama's lemma, so
$A$ is a field. If $d>0$, then $\dim A=d>0$, so $\mathfrak m$ is neither
contained in $\mathfrak m^2$ nor in any of the finitely many minimal primes of
$A$. By prime avoidance there is an $x\in\mathfrak m$ lying outside
$\mathfrak m^2$ and outside every minimal prime. The maximal ideal of $A/(x)$
needs one generator fewer than $\mathfrak m$, while Krull's principal ideal
theorem gives $\dim A/(x)\ge \dim A-1$. With the cotangent-dimension bound this
makes $A/(x)$ regular of dimension $d-1$, hence a domain by induction, so
$(x)$ is a prime ideal. It contains a minimal prime $\mathfrak p$, and
$x\notin\mathfrak p$. If $y\in\mathfrak p$, write $y=ax$; then
$a\in\mathfrak p$ because $\mathfrak p$ is prime. Hence
$\mathfrak p=x\mathfrak p\subseteq\mathfrak m\mathfrak p$, and Nakayama's lemma
gives $\mathfrak p=0$. So $(0)$ is prime.

## Depends on

- [Regular local rings](regular-local-rings.md)

## Proof depends on

- [The cotangent-dimension bound](cotangent-dimension-bound.md)
- Krull's principal ideal theorem, prime avoidance, and Nakayama's lemma.
- Matsumura, *Commutative Ring Theory*, Theorem 14.3.

## Sources

- [Hartshorne II.8, proof of Theorem 8.8, printed pp. 174–175](../../sources/hartshorne-ii-8.md)
