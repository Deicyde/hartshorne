---
article_id: af_4525a69f81e72d0b3853829e
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Ringed.sheafExt Hartshorne.Ringed.sheafExtIsoHomology Hartshorne.Ringed.sheafExtIsoHomology_hom_naturality
---

# Sheaf Ext

For $\mathcal{O}_X$-modules $F,G$, define the $\mathcal{O}_X$-module

$\mathcal{E}xt^n_X(F,G) = R^n \mathcal{H}om_X(F,-)(G)$.

For an injective resolution $G \longrightarrow I^{\bullet}$, identify it naturally with the
degree-$n$ cohomology sheaf of $\mathcal{H}om_X(F,I^{\bullet} )$. This is a sheaf-valued derived
functor, not the global Ext group and not an assumed internal $R\mathcal{H}om$ object.

## Depends on

- [Sheaf Hom as a left-exact functor](module-sheaf-hom-left-exact.md)
- [Right derived functors](../../derived-functors/right-derived-functors.md)
- [Module sheaves have enough injectives](../../sheaf-cohomology/module-sheaves-enough-injectives.md)

## Sources

- [Hartshorne III.6, definition of sheaf Ext, printed p.233](../../../../sources/hartshorne-iii-6.md#definitions-and-restriction-printed-pp233234)
- [Three-model distinction](../../../../sources/hartshorne-iii-6.md#boundary-and-the-three-ext-models)
