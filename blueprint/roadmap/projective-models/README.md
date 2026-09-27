---
article_id: af_becb3ae580c9c99e691ab5a6
---

# Projective models of curves

This 21-leaf milestone covers Hartshorne I.6, Proposition 6.8 through
Corollary 6.12 (printed pp. 43--46), together with the parts of Exercise 3.3
that Theorem 6.9 uses. Ten leaves are statement- and proof-formalized; the
remaining 11 leaves are planned. The preceding 140 leaves remain complete.

The source first extends a map from a punctured abstract nonsingular curve to
a projective target.  It then embeds the complete valuation curve `C_K` in a
product of projective closures of affine models, proves that the resulting
model has exactly the same points, local rings, and function field, and derives
the projective completion and category-equivalence corollaries.

## Source-faithful proof organization

Hartshorne chooses finitely many affine models covering `C_K`.  The existing
normalization milestone already constructed two compatible affine models,
from `k[t]` and `k[t⁻¹]`, whose opens cover `C_K`.  This chapter uses those two
models and the existing binary Segre product.  It is the same finite-cover and
diagonal-closure proof, specialized to a cover already present in the project;
it does not add a separability hypothesis to Theorem 6.9.

Several bridges are intentionally separate leaves: local rings and dimension
of the abstract curve, transport along a `k`-algebra equivalence, the exact
Exercise 3.3 criteria, and existence of a function-field DVR dominating a
curve local ring.  In particular, the local-ring comparison is made inside a
common function field rather than replacing inclusions by abstract
isomorphisms.

## Valuation and morphism prerequisites

- [Regularity near a valuation](regular-near-valuation.md)
- [The local ring of an abstract curve](abstract-curve-local-ring.md)
- [Abstract valuation curves have dimension one](abstract-curve-dimension.md)
- [Transporting valuation curves along a field equivalence](valuation-space-field-equivalence.md)
- [Dense morphisms inject on local rings](dominant-morphism-local-ring.md)
- [Isomorphisms from topology and local rings](isomorphism-local-criterion.md)
- [A projective coordinate pivot](valuation-projective-pivot.md)

## Proposition 6.8 and Theorem 6.9

- [Extension to a projective target](projective-extension.md)
- [A two-chart affine cover of the valuation curve](two-affine-chart-cover.md)
- [Extensions to the projective chart closures](projective-chart-extensions.md)
- [The projective diagonal model](projective-diagonal.md)
- [The function field of the diagonal model](projective-model-function-field.md)
- [Local rings of the diagonal model](projective-model-local-rings.md)
- [A dominating function-field DVR](dominating-dvr.md)
- [Nonsingular projective models of function fields](function-field-projective-model.md)

## Corollaries 6.10--6.12

- [Abstract curves are quasi-projective](abstract-curve-quasiprojective.md)
- [Completion of a nonsingular curve](nonsingular-curve-projective-open.md)
- [Projective models of curves](curve-projective-model.md)
- [The three curve categories](curve-categories.md)
- [Extension of dominant rational maps](projective-rational-map-extension.md)
- [The curve/function-field category equivalence](curve-category-equivalence.md)

## Mathlib boundary

The current APIs provide projective closure, the binary Segre product,
function-field functoriality, local-ring maps, the valuation-space curve, and
Krull--Akizuki.  Missing project-facing bridges are precisely the leaves above.
The projective chart criterion and `VarietyHom.codRestrictProj` already exist
but should be re-exported from an import-neutral module when Proposition 6.8
is implemented.  No arbitrary heterogeneous finite product is required.
