---
article_id: af_b9a7e8ef4ead61f0fe3a8d41
---

# Normalization and the valuation-space curve

This milestone continues Hartshorne I.6 from Lemma 6.5 through Proposition
6.7.  It first proves the two quoted integral-closure results used in the
construction: Theorem 3.9A, finiteness of normalization for a finitely
generated domain over a field, and Theorem 6.3A, preservation of the Dedekind
property in a finite extension of the fraction field.

For a one-dimensional function field `K/k`, let `C_K` be the discrete
valuation rings of `K` containing `k`.  Lemma 6.5 says that every element of
`K` has only finitely many poles on `C_K`.  Corollary 6.6 realizes each point
of `C_K` as the local ring of a point on a nonsingular affine curve.

The second phase equips `C_K` with its cofinite topology and defines regular
functions on an open set `U` by the intersection of its valuation rings.
Proposition 6.7 then identifies every nonsingular quasi-projective curve with
an open subcurve of this valuation space.

## Mathlib boundary

The pinned Mathlib proves finiteness and the Dedekind property of an integral
closure only for a finite *separable* extension, through
`IsIntegralClosure.finite` and
`IsIntegralClosure.isDedekindDomain`.  Hartshorne imposes no separability
hypothesis.  The roadmap therefore isolates the purely inseparable
normalization argument and the Krull--Akizuki theorem instead of marking
either source theorem as already formalized upstream.

Mathlib does provide the remaining algebraic and topological primitives:
integral closures are integrally closed and have the expected fraction field
without a separability assumption, ideals in a Dedekind domain have finite
support, and `CofiniteTopology` is irreducible on an infinite type.

The geometric branch below does not wait for the two exact nonseparable
background theorems. A fixed separating parameter `t` makes `K/k(t)` finite
separable, so Mathlib constructs finite Dedekind normalizations for both
`k[t]` and `k[t⁻¹]`. Every valuation ring contains one of `t` and `t⁻¹`, and
these two affine charts suffice for Lemma 6.5, Corollary 6.6, and Proposition
6.7. Theorems 3.9A and 6.3A remain in scope as independent source-facing
branches.

## Finiteness of normalization

- [Frobenius is finite on an affine algebra over a perfect field](frobenius-finite-affine-algebra.md)
- [Purely inseparable normalizations are finite](purely-inseparable-normalization-finite.md)
- [Normalizations of polynomial rings are finite](polynomial-normalization-finite.md)
- [Finiteness of integral closure](finite-integral-closure.md)

## Krull--Akizuki and Dedekind normalization

- [Finite-length quotients in Krull--Akizuki](krull-akizuki-quotient-finite.md)
- [The Krull--Akizuki theorem](krull-akizuki.md)
- [Integral closures of Dedekind domains](dedekind-integral-closure.md)

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
- [The cofinite valuation space](valuation-space-topology.md)
- [Residue fields of function-field DVRs](valuation-residue-field.md)
- [Regular functions on the valuation space](valuation-regular-functions.md)
- [The valuation-space regularity axioms](valuation-regular-functions-local.md)
- [Abstract nonsingular curves](abstract-nonsingular-curve.md)
- [The function field of an abstract nonsingular curve](valuation-space-function-field.md)
- [Nonsingular affine curves have Dedekind coordinate rings](nonsingular-affine-curve-dedekind.md)
- [The local-ring map has open image](curve-local-ring-map-open.md)
- [Nonsingular curves are open subcurves of their valuation spaces](curve-to-valuation-space-iso.md)

## Scope note

This milestone stops at Proposition 6.7 on printed p. 43.  Proposition 6.8,
extension of morphisms across a missing point, begins the separate projective-
model milestone leading to Theorem 6.9 and Corollaries 6.10--6.12.  The
exercises remain out of scope except for the weak infinitude consequence of
Exercise 4.8 used in Hartshorne's construction of `C_K`.
