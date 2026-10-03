---
declaration: theorem
origin: bridged
source_units: [chapter-iv-section-4]
---

# A relative degree-one divisor is a graph

Let `T` be a finite-type scheme, not necessarily reduced, and let
`Z subset X times T` be an effective relative Cartier divisor, flat over
`T`, whose fibre over every `t : T` has degree one. Then `Z -> T` is an
isomorphism and `Z` is the graph of a unique morphism `T -> X`.

This isolates the scheme-theoretic step hidden by Hartshorne's phrase “one
sees easily”; a bijection on closed fibres alone is insufficient over a
nonreduced parameter scheme.

## Depends on

- [Effective Cartier divisors and locally principal subschemes](../../../schemes/divisors/cartier-picard/effective-cartier-closed-subscheme.md)
- [Cohomology and base change](../../../cohomology/semicontinuity/theorems/cohomology-and-base-change.md)
- [Projective quasi-finite morphisms are finite](../../../cohomology/formal-functions/applications/projective-quasifinite-finite.md)
- [Finite locally free modules over local rings are free](../../../cohomology/flat-families/flatness/finite-flat-local-module-free.md)

## Proof depends on

- The relative-Cartier hypothesis supplies flatness, while degree-one fibres
  make the projective morphism `Z -> T` quasi-finite and hence finite.
- Cohomology and base change makes the pushforward of `O_Z` locally free of
  rank one and identifies the unit map `O_T -> p_*O_Z` fibrewise; Nakayama
  upgrades it to an isomorphism.
- A finite morphism with structure algebra `O_T` is an isomorphism, and the
  closed immersion in `X times T` is then the graph of its first projection.

## Sources

- [Hartshorne IV.4, proof of Theorem 4.11, pp.325–326](../../../../sources/hartshorne-iv-4.md)
