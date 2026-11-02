---
article_id: af_9ccfa4b4af1188a70942772f
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.separableNormalizationCharts
---

# The two separable normalization charts

Fix a separating parameter $t$ for the one-dimensional function field $K/k$.
Let $B_0$ and $B_{\infty}$ be the integral closures of $k[t]$ and $k[t^{-1}]$
in $K$, respectively:

$B_{0} = \overline{k[t]}^{K}$ and
$B_{\infty}=\overline{k[t^{-1}]}^{K}$.

Both rings are finite over their polynomial base, finitely generated over
$k$, Dedekind of exact Krull dimension one, and have fraction field $K$.

The separating-parameter theorem makes both fraction-field extensions
finite and separable, so the separable integral-closure theorems apply.
Dimension one follows from invariance under an integral extension of a
one-variable polynomial ring. The equality $k(t^{-1})=k(t)$ gives the
second chart. Every valuation ring of $K$ contains $t$ or $t^{-1}$, so the
two normalization charts cover $C _K$.

## Depends on

- [One-dimensional function fields have separating parameters](separating-parameter.md)
- [Discrete valuation rings of a function field](function-field-dvrs.md)

## Proof depends on

- [Krull dimension is invariant under integral extensions](../affine-varieties/dimension-integral-extension.md)

## Sources

- [Hartshorne I.6, normalization construction in Lemma 6.5 and Corollary 6.6 (pp. 41--42)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
