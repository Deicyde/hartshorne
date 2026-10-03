---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Frobenius is ramified everywhere

Let `f : Y^p -> Y` be one `k`-linear Frobenius step for a curve in
characteristic `p`. It is the identity on points, and every point has
ramification index `p`. The map

`f^* Omega_Y -> Omega_(Y^p)`

is zero, so `Omega_((Y^p)/Y) ~= Omega_(Y^p)`.

This map is inseparable. Its relative differential sheaf has rank one rather
than finite torsion support, so the separable ramification divisor is not
defined for it.

## Depends on

- [The ramification-index bridge](ramification-index-bridge.md)
- [Absolute Frobenius and Hartshorne's Frobenius twist](scheme-frobenius-twist.md)
- [The transitivity sequence for differential sheaves](../../schemes/differentials/scheme-differentials/relative-differentials-transitivity.md)

## Proof depends on

- A uniformizer pulls back to its `p`th power and `d(t^p)=0` in
  characteristic `p`.

## Sources

- [Hartshorne IV.2, Example 2.5.1, p.303](../../../sources/hartshorne-iv-2.md#consequences-pp302303)
