---
article_id: af_e31d8787e86350185ec8ff60
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.abstractNonsingularCurve
---

# Abstract nonsingular curves

Let $k$ be algebraically closed and let $K/k$ be a finitely generated
field extension of transcendence degree one. An *abstract nonsingular
curve* is a nonempty open subset $U$ of the cofinite valuation space $C_K$,
with its induced topology and regular functions given on open subsets by

$$\mathcal O(U')=\bigcap_{R\in U'}R,$$

read as $k$-valued functions by residue evaluation.

The nonempty cofinite open $U$ is irreducible. Its regular functions
satisfy restriction, closedness of zero loci, division by a nowhere-zero
function, and locality. On the empty open, the intersection is all of $K$
and residue evaluation gives the unique empty function; injectivity of
evaluation applies only to nonempty opens.

The definition does not assume quasi-projectivity. That is obtained later
by the comparison with projective models.

## Depends on

- [The cofinite valuation space](valuation-space/valuation-space-topology.md)
- [Regular functions on the valuation space](valuation-regular-functions.md)

## Proof depends on

- [The valuation-space regularity axioms](valuation-regular-functions-local.md)
- [The valuation space is infinite](valuation-space/valuation-space-infinitude.md)

## Sources

- [Hartshorne I.6, definition of an abstract nonsingular curve (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
