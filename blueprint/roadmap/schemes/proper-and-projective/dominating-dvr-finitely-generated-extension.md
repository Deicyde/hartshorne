---
article_id: af_f3a7028c4c4728ad41df66fb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_dominating_dvr_of_fg_of_ne_bot_or_transcendental Hartshorne.exists_dominating_dvr_of_fg
---

# A dominating DVR in a finitely generated extension

Let $(A,\mathfrak{m} )$ be a Noetherian local domain, let
$K = \operatorname{Frac} (A)$, and let $L/K$ be a finitely generated field extension.
Suppose that either $\mathfrak{m} \neq 0$ or $L$ is not algebraic over $K$. Then
there is a nonfield discrete valuation ring $R$ with fraction field $L$ which
dominates the image of $A$ in $L$.

This is the project-authored repair of Exercise 4.11(a) used by the geometric
criterion. Without the added hypothesis, the literal statement is false exactly
when $A$ is a field and $L/K$ is algebraic, for instance when $L=K$: every ring
between $K$ and an algebraic extension $L$ is a field.
That $A$ is a domain also follows from its having the fraction field $K$, so
the proof never invokes that hypothesis separately.

Adjoin a transcendence basis and localize a polynomial ring over $A$ to reduce
to the case that $L$ is finite over the new fraction field. Apply the
one-dimensional-local-overring theorem. Its integral closure in $L$ is
Noetherian and at most one-dimensional by Krull–Akizuki. Lying over supplies a
maximal ideal above the original one; localizing there gives a one-dimensional
integrally closed Noetherian local domain, hence a nonfield DVR, and preserves
domination.

If $\mathfrak{m} = 0$, then $A = K$ and some $t \in L$ is transcendental over $K$.
The localization of $K[t]$ at $(t)$ is a Noetherian local domain in $L$ with
nonzero maximal ideal, and $L$ is finitely generated over its fraction field
$K(t)$; the first case gives a DVR dominating it, and this DVR contains $K$,
which is all that domination of the field $A$ requires.

## Depends on

- No project-local statement prerequisites.

## Proof depends on

- [A one-dimensional local overring](one-dimensional-local-overring.md)
- [The Krull--Akizuki theorem](../../curve-normalization/krull-akizuki/krull-akizuki.md)
- [Characterizations of discrete valuation rings](../../nonsingular-curves/dvr-characterizations.md)
- Lying over for the integral closure in a finite field extension.

## Sources

- [Hartshorne II.4, repaired Exercise 4.11(a)](../../../sources/hartshorne-ii-4.md#adopted-exercises)
