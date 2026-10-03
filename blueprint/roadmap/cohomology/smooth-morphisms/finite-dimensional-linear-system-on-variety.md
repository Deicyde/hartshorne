---
declaration: structure
origin: bridged
source_units: [chapter-iii-section-10]
---

# Finite-dimensional linear systems on an arbitrary variety

Let `X` be an integral finite-type scheme over a field, `L` an invertible
sheaf, and `V` a finite-dimensional subspace of `Gamma(X,L)`. Construct its
scheme-theoretic base locus. On the complement, the evaluation map is
surjective and defines a morphism to the projective space `P(V)` such that the
zero scheme of every nonzero section in `V` is the pullback of its parameter
hyperplane.

If `X` is nonsingular, each nonzero section has an effective Cartier zero
scheme away from components on which it vanishes identically. This API does
not assume `X` is projective; it is the representation bridge needed for
Remark 10.9.2.

## Depends on

- [Locally free module sheaves](../../schemes/modules-and-quasicoherent/locally-free-and-invertible.md)
- [Effective Cartier divisors as closed subschemes](../../schemes/divisors/cartier-picard/effective-cartier-closed-subscheme.md)
- [Projective space over a scheme](../../schemes/proper-and-projective/projective-space-over-scheme.md)

## Sources

- [Hartshorne III.10, Corollary 10.9 and Remark 10.9.2, pp.274–275](../../../sources/hartshorne-iii-10.md#homogeneous-spaces-kleiman-and-bertini-pp272275)
