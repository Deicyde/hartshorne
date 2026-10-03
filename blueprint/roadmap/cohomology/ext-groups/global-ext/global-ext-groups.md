---
declaration: definition
origin: cited
source_units: [chapter-iii-sections-6-7]
mathlib: true
mathlib_declaration: CategoryTheory.Abelian.Ext
mathlib_file: Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean
---

# Global Ext groups

Fix a universe `w` and an explicit instance
`HasExt.{w} (Scheme.Modules X)`. For `O_X`-modules `F` and `G`, define
`Ext^n_X(F,G) : Type w` as the degree-`n` global Ext group in `X.Modules`,
functorial contravariantly in `F` and covariantly in `G`. In degree zero it is
naturally `Hom_X(F,G)`, and positive Ext into an injective object vanishes.

The main result is the global Ext definition. Pinned Mathlib supplies it as
`CategoryTheory.Abelian.Ext`; `Ext.addEquiv₀`, `Abelian.extFunctor`, and
`Ext.eq_zero_of_injective` supply the stated supporting API.

## Depends on

- [Sheaves of modules](../../../schemes/modules-and-quasicoherent/sheaves-of-modules.md)

## Proof depends on

- [Module sheaves have enough injectives](../../sheaf-cohomology/module-sheaves-enough-injectives.md)
- Pinned Mathlib's `CategoryTheory.hasExt_of_enoughInjectives`, with a chosen
  local-smallness universe, supplies the required `HasExt` instance.

## Sources

- [Hartshorne III.6, definition, printed p.233](../../../../sources/hartshorne-iii-6.md#definitions-and-restriction-printed-pp233234)
