---
article_id: af_dc1508fedff9a089a2641a04
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.FunctionFieldDVR.finite_hasPoleAt Hartshorne.FunctionFieldDVR.finite_vanishesAt Hartshorne.FunctionFieldDVR.finite_mem_maximalIdeal
---

# A rational function has finitely many poles

Let $K/k$ be a one-dimensional function field and let $x\in K$.  Then

$\{R \in C _K | x \notin R\}$

is finite.  This is Lemma 6.5.

Choose a separating parameter $t$ and the two finite Dedekind normalizations
of $k[t]$ and $k[t^{-1}]$. Every valuation ring contains $t$ or $t^{-1}$, so
these two charts cover $C _K$. On either chart, write $x = a/b$ in the fraction
field of the normalization. If $x$ does not belong to the localization at a
center $\mathfrak p$, then $b\in\mathfrak p$. Distinct DVRs have distinct centers, and only
finitely many maximal ideals contain the nonzero principal ideal $(b)$, by
finite factorization of ideals in a Dedekind domain. Taking the union of the
two finite exceptional sets proves the result.

The proof also establishes the companion statement used in [Proposition I.6.7](curve-to-valuation-space-iso.md):
for $0\ne x\in K$, only finitely many $R \in C _K$ have $x \in \mathfrak{m} _R$.


## Depends on

- [Discrete valuation rings of a function field](function-field-dvrs.md)

## Proof depends on

- [The two separable normalization charts](separable-normalization-charts.md)
- [A DVR containing a Dedekind subring is its localization](dedekind-subring-localization.md)

## Sources

- [Hartshorne I.6, Lemma 6.5 (p. 41)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
