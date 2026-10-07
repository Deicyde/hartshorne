## README.md

### Mathlib boundary

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
