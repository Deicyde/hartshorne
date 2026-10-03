---
declaration: theorem
origin: cited
source_units: [chapter-ii-section-5]
---

# The affine-local criterion for quasi-coherence

For an `𝒪_X`-module `F`, prove the equivalence of the following conditions:

1. `F` has Mathlib's local-presentation quasi-coherence predicate;
2. `X` has an affine open cover on which `F` is isomorphic to `M̃`; and
3. for every affine open `U = Spec A`, the restriction `F|_U` is isomorphic
   to `Γ(U,F)̃`.

This is Hartshorne's definition and Proposition 5.4, with Exercise 5.4 used
only to bridge the chosen Mathlib representation.  The completion result is
the three-way equivalence, not a second definition of quasi-coherence.

## Depends on

- [Modules and quasi-coherent sheaves on an affine scheme](affine-quasicoherent-equivalence.md)
- [Quasi-coherence by local presentations](quasicoherent-local-presentations.md)

## Proof depends on

- Quasi-coherence is preserved by restriction to an open subscheme and is
  local on an open cover.
- Affine opens form a basis for the topology of a scheme.

## Sources

- [Hartshorne II.5, definition and Proposition 5.4 on printed pp. 111–113](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
