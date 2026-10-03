---
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# A dominating DVR in a finitely generated extension

Let `(A,𝔪)` be a Noetherian local domain with nonzero maximal ideal, let
`K = Frac(A)`, and let `L/K` be a finitely generated field extension. Then
there is a nonfield discrete valuation ring `R` with fraction field `L` which
dominates the image of `A` in `L`.

This is the project-authored repair of Exercise 4.11(a) used by the geometric
criterion. Without the nonzero-maximal-ideal hypothesis, the literal statement
is false when `A` is a field and `L=K`.

Adjoin a transcendence basis and localize a polynomial ring over `A` to reduce
to the case that `L` is finite over the new fraction field. Apply the
one-dimensional-local-overring theorem. Its integral closure in `L` is
Noetherian and at most one-dimensional by Krull–Akizuki. Lying over supplies a
maximal ideal above the original one; localizing there gives a one-dimensional
integrally closed Noetherian local domain, hence a nonfield DVR, and preserves
domination.

## Depends on

- No project-local statement prerequisites.

## Proof depends on

- [A one-dimensional local overring](one-dimensional-local-overring.md)
- [The Krull--Akizuki theorem](../../curve-normalization/krull-akizuki/krull-akizuki.md)
- [Characterizations of discrete valuation rings](../../nonsingular-curves/dvr-characterizations.md)
- Lying over for the integral closure in a finite field extension.

## Sources

- [Hartshorne II.4, repaired Exercise 4.11(a)](../../../sources/hartshorne-ii-4.md#adopted-exercises)
