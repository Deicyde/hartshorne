---
declaration: def
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# Associated points of a scheme

A point `x` of a locally Noetherian scheme `X` is associated when the maximal
ideal of the local ring `O_{X,x}` is an associated prime of the zero module.
Equivalently, every element of that maximal ideal is a zero-divisor.

## Depends on

- [Locally Noetherian schemes](../../../schemes/first-properties/locally-noetherian.md)
- [The local ring of a scheme](../../../schemes/spectrum-and-schemes/spec-stalk.md)

## Proof depends on

- `IsAssociatedPrime`, `isAssociatedPrime_iff`, and
  `biUnion_associatedPrimes_eq_compl_nonZeroDivisors` from
  `Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`.

## Sources

- [Hartshorne III.9, definition on p.257](../../../../sources/hartshorne-iii-9.md#dimensions-associated-points-and-flat-limits-pp256261)
