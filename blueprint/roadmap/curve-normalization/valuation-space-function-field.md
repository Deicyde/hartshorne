---
article_id: af_8050d89a6a44d6f922db6a21
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.abstractNonsingularCurveToFunctionFieldAlgHom_bijective
---

# The function field of an abstract nonsingular curve

Let $k$ be algebraically closed, let $K/k$ be an essentially finite-type field
extension with transcendence degree one, and let $U$ be a nonempty open subset
of $C _K$.  The function field of the associated abstract nonsingular curve is
canonically isomorphic to $K$ as a $k$-algebra.

Every $f\in K$ lies in all but finitely many valuation rings by [Lemma I.6.5](finite-poles.md), so it
is regular on a nonempty open subset of $U$ and defines a rational function.
Conversely, every rational representative on the abstract curve is represented
by a unique element of $K$, because residue evaluation is injective on
nonempty opens.  These constructions respect equivalence of rational representatives and
give inverse algebra maps.

## Depends on

- [Abstract nonsingular curves](abstract-nonsingular-curve.md)

## Proof depends on

- [A rational function has finitely many poles](finite-poles.md)
- [Regular functions on the valuation space](valuation-regular-functions.md)
- [The valuation space is infinite](valuation-space/valuation-space-infinitude.md)

## Sources

- [Hartshorne I.6, identification of the function field of $C _K$ with $K$ (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
