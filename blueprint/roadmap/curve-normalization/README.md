---
article_id: af_b9a7e8ef4ead61f0fe3a8d41
---

# Normalization and the valuation-space curve

This milestone continues Hartshorne I.6 from [Lemma I.6.5](finite-poles.md) through Proposition
6.7.  It first proves the two quoted integral-closure results used in the
construction: [Theorem I.3.9A](finite-integral-closure.md), finiteness of normalization for a finitely
generated domain over a field, and [Theorem I.6.3A](krull-akizuki/dedekind-integral-closure.md), preservation of the Dedekind
property in a finite extension of the fraction field.

For a one-dimensional function field $K/k$, let $C _K$ be the discrete
valuation rings of $K$ containing $k$.  [Lemma I.6.5](finite-poles.md) says that every element of
$K$ has only finitely many poles on $C _K$.  [Corollary I.6.6](dvr-affine-model.md) realizes each point
of $C _K$ as the local ring of a point on a nonsingular affine curve.

All 26 leaves in this milestone are formalized. They include the nonseparable
normalization theorems, finite poles and affine DVR models, the complete
regular-function structure on the valuation space, the abstract curve and its
function field, and [Proposition I.6.7](curve-to-valuation-space-iso.md) as an isomorphism of varieties.

The second phase equips $C _K$ with its cofinite topology and defines regular
functions on an open set $U$ by the intersection of its valuation rings.
[Proposition I.6.7](curve-to-valuation-space-iso.md) then identifies every nonsingular quasi-projective curve with
an open subcurve of this valuation space.


## Two affine charts and the algebraic background

A separating parameter $t$ makes $K/k(t)$ finite and separable.
The integral closures of $k[t]$ and $k[t^{-1}]$ give two Dedekind affine
models. Every valuation ring contains $t$ or $t^{-1}$, so these models
cover the valuation space. They suffice for the finite-pole theorem,
local affine models, and the open-subcurve comparison.

The general normalization theorems remain separate: Hartshorne's
Theorems I.3.9A and I.6.3A do not impose separability. Their proofs use the
purely inseparable normalization argument and Krull–Akizuki.

## Finiteness of normalization

- [Frobenius is finite on an affine algebra over a perfect field](frobenius-finite-affine-algebra.md)
- [Purely inseparable normalizations are finite](purely-inseparable-normalization-finite.md)
- [Normalizations of polynomial rings are finite](polynomial-normalization-finite.md)
- [Finiteness of integral closure](finite-integral-closure.md)

## Krull--Akizuki and Dedekind normalization

- [Krull--Akizuki and Dedekind normalization](krull-akizuki/README.md)

## Finite poles and affine models

- [Discrete valuation rings of a function field](function-field-dvrs.md)
- [One-dimensional function fields have separating parameters](separating-parameter.md)
- [The two separable normalization charts](separable-normalization-charts.md)
- [A DVR containing a Dedekind subring is its localization](dedekind-subring-localization.md)
- [Dedekind localizations occur on nonsingular affine curves](dedekind-affine-model.md)
- [A rational function has finitely many poles](finite-poles.md)
- [Every function-field DVR has a nonsingular affine model](dvr-affine-model.md)

## The valuation-space curve

- [Quasi-projective curves have the cofinite topology](quasiprojective-curve-cofinite.md)
- [Valuation-space topology](valuation-space/README.md)
- [Residue fields of function-field DVRs](valuation-residue-field.md)
- [Regular functions on the valuation space](valuation-regular-functions.md)
- [The valuation-space regularity axioms](valuation-regular-functions-local.md)
- [Abstract nonsingular curves](abstract-nonsingular-curve.md)
- [The function field of an abstract nonsingular curve](valuation-space-function-field.md)
- [Nonsingular affine curves have Dedekind coordinate rings](nonsingular-affine-curve-dedekind.md)
- [The local-ring map has open image](curve-local-ring-map-open.md)
- [Nonsingular curves are open subcurves of their valuation spaces](curve-to-valuation-space-iso.md)

## Scope note

This milestone stops at [Proposition I.6.7](curve-to-valuation-space-iso.md) on printed p. 43.  [Proposition I.6.8](../projective-models/projective-extension.md),
extension of morphisms across a missing point, begins the separate projective-
model milestone, now decomposed through [Theorem I.6.9](../projective-models/function-field-projective-model.md) and Corollaries
6.10--6.12.  The exercises remain out of scope except for the weak infinitude
consequence of Exercise 4.8 used in Hartshorne's construction of $C _K$.
