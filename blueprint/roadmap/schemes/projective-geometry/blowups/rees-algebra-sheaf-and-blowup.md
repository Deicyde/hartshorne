---
article_id: af_052e65e0f47f741780a4beb9
declaration: def
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Rees algebras and blowups

For a coherent ideal sheaf `I` on a Noetherian scheme `X`, construct the
quasi-coherent graded Rees algebra `R(I) = direct-sum_{d >= 0} I^d` and define
the blowup `Bl_I(X) = Proj_X R(I)` with its projection to `X`.

Keep the module pullback `f^*I` distinct from the inverse-image ideal, which is
the image of `f^*I -> O` and is represented by `IdealSheafData.comap`.

## Depends on

- [Relative Proj](../relative-proj-bundles/relative-proj.md)
- [Module and ideal-sheaf data](../../coherent-sheaves/module-ideal-sheaf-data.md)

## Proof depends on

- `reesAlgebra`, `adjoin_monomial_eq_reesAlgebra`, and its finite-type result
  on affine charts.

## Sources

- [Hartshorne II.7, blowup and inverse-image-ideal definitions (p.163)](../../../../sources/hartshorne-ii-7.md#blowups)
- [Stacks Project, blowing up, tag 01OF](../../../../sources/hartshorne-ii-7.md#adopted-auxiliary-proof-sources)
