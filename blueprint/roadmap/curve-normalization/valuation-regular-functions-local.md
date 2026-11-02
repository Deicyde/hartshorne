---
article_id: af_0fdccec34faa6f6a85264973
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.regularFunctions_axioms
---

# The valuation-space regularity axioms

Let $k$ be algebraically closed and let $K/k$ be a finitely generated
field extension of transcendence degree one. Regular functions on open
subsets of $C_K$ have the following properties:

1. They restrict to smaller open subsets.
2. Their zero loci are closed.
3. Division by a nowhere-zero regular function preserves regularity.
4. Regularity is local.

Restriction follows from inclusion of the corresponding intersections of
valuation rings. A nonzero rational function vanishes at only finitely many
valuations, so its zero locus is closed. A denominator with nonzero residue
at $R$ is a unit in $R$, proving the division property.

For locality, choose one local rational representative. Every other
representative agrees with it on a nonempty intersection of cofinite
opens. Injectivity of residue evaluation identifies the corresponding
elements of $K$, so the chosen representative belongs to every valuation
ring over the original open set and represents the whole function.

## Depends on

- [Regular functions on the valuation space](valuation-regular-functions.md)

## Proof depends on

- [A rational function has finitely many poles](finite-poles.md)
- [The valuation space is infinite](valuation-space/valuation-space-infinitude.md)

## Sources

- [Hartshorne I.6, regular functions on $C _K$ and their identification with functions (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
