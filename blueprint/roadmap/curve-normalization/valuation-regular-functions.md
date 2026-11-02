---
article_id: af_9d9ddee15270ff39e2460179
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.regularFunctions
---

# Regular functions on the valuation space

Let $k$ be algebraically closed, let $K/k$ be a finitely generated field
extension of transcendence degree one, and let $U\subseteq C_K$ be open.
The algebra of rational functions regular on $U$ is

$$\mathcal O_K(U)=\bigcap_{R\in U}R\subseteq K.$$

Residue evaluation at each $R\in U$ gives a $k$-valued function on $U$.
The regular functions on $U$ form the image of this evaluation map.

For nonempty $U$, evaluation is injective. If two rational functions have
equal residues everywhere, their difference belongs to $\mathfrak m_R$
for every $R\in U$. A nonzero rational function can vanish at only finitely
many valuations, while a nonempty cofinite open is infinite, so the
difference must be zero.

For $U=\varnothing$, the intersection is all of $K$ and evaluation gives
the unique empty function. Its image is the full function algebra on the
empty set; injectivity is not asserted in this case.

## Depends on

- [The cofinite valuation space](valuation-space/valuation-space-topology.md)
- [Residue fields of function-field DVRs](valuation-residue-field.md)

## Proof depends on

- [A rational function has finitely many poles](finite-poles.md)
- [The valuation space is infinite](valuation-space/valuation-space-infinitude.md)

## Sources

- [Hartshorne I.6, regular functions on open subsets of $C _K$ (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
