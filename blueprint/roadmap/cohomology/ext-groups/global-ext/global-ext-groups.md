---
article_id: af_585e8ad059d75374368d3f37
declaration: definition
origin: cited
mathlib: true
mathlib_declaration: CategoryTheory.Abelian.Ext
mathlib_file: Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean
---

# Global Ext groups

Assume that Ext groups exist in the category of
$\mathcal{O}_X$-modules. For module sheaves $F$ and $G$, define
$\operatorname{Ext}^n_X(F,G)$ to be the degree-$n$ global Ext
group. It is contravariant in $F$ and covariant in $G$. In degree
zero it is naturally $\operatorname{Hom}_X(F,G)$, and positive
Ext into an injective object vanishes.

## Depends on

- [Sheaves of modules](../../../schemes/modules-and-quasicoherent/sheaves-of-modules.md)

## Proof depends on

- [Module sheaves have enough injectives](../../sheaf-cohomology/module-sheaves-enough-injectives.md)
- Enough injectives provide the Ext construction in a locally small abelian category.

## Sources

- [Hartshorne III.6, definition, printed p.233](../../../../sources/hartshorne-iii-6.md#definitions-and-restriction-printed-pp233234)
