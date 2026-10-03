---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
---

# Injectives restrict to open subsets

Let `j : U ↪ X` be an open inclusion. If `J` is injective in `X.Modules`,
then its restriction `J|_U` is injective in `U.Modules`.

No coherence or finite-presentation hypothesis is imposed. Restriction is the
module-sheaf functor along the restricted structure sheaf, not merely
restriction of the underlying abelian sheaf.

## Depends on

- [Sheaves of modules](../../../schemes/modules-and-quasicoherent/sheaves-of-modules.md)
- [Open extension by zero](../../../schemes/sheaf-functors/open-extension-by-zero.md)

## Proof depends on

- Lift open extension by zero to module sheaves, prove it is left adjoint to
  restriction, and prove it preserves monomorphisms. The right adjoint then
  preserves injective objects.

## Sources

- [Hartshorne III.6, Lemma 6.1, printed p.233](../../../../sources/hartshorne-iii-6.md#definitions-and-restriction-printed-pp233234)
