---
article_id: af_c6bf0d8d37f0cc07eedc10f3
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.FunctionFieldDVR Hartshorne.FunctionFieldDVR.HasPoleAt Hartshorne.FunctionFieldDVR.VanishesAt
---

# Discrete valuation rings of a function field

For a field extension $K/k$, let $C_K$ be the set of discrete valuation
rings $R\subseteq K$ containing the image of $k$.

Containing $k$ is equivalent to the corresponding valuation being trivial
on nonzero elements of $k$. An element $x\in K$ has a *pole* at $R$ if
$x\notin R$, and *vanishes* at $R$ if $x\in\mathfrak m_R$.

A point of $C_K$ is specified by its valuation ring: equivalent valuations
with the same ring describe the same point.

## Depends on

No project-local statement prerequisites.

## Sources

- [Hartshorne I.6, definition of $C _K$ and of valuation rings of $K/k$ (pp. 39--42)](../../sources/hartshorne.md#i6-normalization-and-finite-poles)
