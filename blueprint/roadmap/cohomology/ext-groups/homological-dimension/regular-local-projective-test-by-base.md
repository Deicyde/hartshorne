---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
---

# Projectivity detected by Ext against the base ring

Let `A` be a Noetherian regular local ring and `M` a finitely generated
`A`-module. Then `M` is projective if and only if
`Ext^i_A(M,A)=0` for every `i>0`.

## Depends on

- [Projective dimension detected by Ext](projective-dimension-ext-criterion.md)
- [The global dimension of a regular local ring](regular-local-global-dimension.md)

## Proof depends on

- Descending induction on degree to pass from Ext vanishing against `A` to
  Ext vanishing against every finite module.
- Splitting a finite free presentation once `Ext^1` vanishes.

## Sources

- [Hartshorne III, Exercise 6.6(a), printed p.238](../../../../sources/hartshorne-iii-6.md#adopted-exercises-printed-pp237238)
