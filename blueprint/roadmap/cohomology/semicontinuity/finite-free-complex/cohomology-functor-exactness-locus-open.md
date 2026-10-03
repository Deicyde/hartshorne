---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# The exactness loci are open

Let `y_0` correspond to `p : Spec A`. Restrict `T^i` to `A_p`-modules by

`T^i_p(N) = H^i(L_p tensor_(A_p) N)`.

If `T^i_p` is left exact, respectively right exact or exact, then there is an
open neighbourhood `U` of `y_0` such that the corresponding localized functor
has the same property at every `y in U`.

## Depends on

- [Left exact cohomology functors are finitely represented](left-exact-cohomology-functor-representability.md)
- [Right exactness and the cohomology-tensor comparison](cohomology-tensor-comparison-right-exact.md)
- [Exactness of a cohomology functor](cohomology-functor-exactness-criterion.md)
- [The free locus of a coherent sheaf](../../../schemes/coherent-sheaves/coherent-free-locus.md)

## Proof depends on

- Left exactness is openness of the free locus of `W^i`; right exactness of
  `T^i` is left exactness of `T^(i+1)` by the long exact sequence; exactness is
  their conjunction.
- Flat base change identifies the localized complex functor with the functor
  attached to `X times_Y Spec O_(Y,y) -> Spec O_(Y,y)`.

## Sources

- [Hartshorne III.12, Proposition 12.7, p.287](../../../../sources/hartshorne-iii-11-12.md#cohomology-after-tensor-and-finite-free-models-pp281287)
