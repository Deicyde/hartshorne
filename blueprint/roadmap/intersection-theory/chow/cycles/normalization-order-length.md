---
article_id: af_dbe213d5c86308cea9ace1ec
declaration: theorem
origin: background
---

# Orders via the normalization are lengths

Let $A$ be a one-dimensional Noetherian local domain with fraction field $K$
and residue field $\kappa$, and suppose the integral closure $B$ of $A$ in $K$
is a finite $A$-module. Then $B$ has finitely many maximal ideals
$\mathfrak m_1,\ldots,\mathfrak m_s$, each localization $B_{\mathfrak m_i}$ is a
discrete valuation ring, and for every nonzero $a\in A$

$\ell_A(A/aA)=\sum_{i=1}^s\operatorname{ord}_{B_{\mathfrak m_i}}(a)\,[\kappa(\mathfrak m_i):\kappa]$.

The quotient $B/A$ is killed by a nonzero element of $A$, so it has finite
length, and the snake lemma for multiplication by $a$ on
$0\to A\to B\to B/A\to 0$ gives $\ell_A(A/aA)=\ell_A(B/aB)$. The ring $B$ is a
semilocal Dedekind domain, so
$B/aB\cong\prod_i B_{\mathfrak m_i}/aB_{\mathfrak m_i}$, whose $i$-th factor has a
composition series of $\operatorname{ord}_{B_{\mathfrak m_i}}(a)$ copies of
$\kappa(\mathfrak m_i)$, each of $A$-length $[\kappa(\mathfrak m_i):\kappa]$.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Krull dimension is invariant under integral extensions](../../../affine-varieties/dimension-integral-extension.md)

## Sources

- Fulton, *Intersection Theory*, Example 1.2.3 and Lemma A.3 (numbering not confirmed against the text).
