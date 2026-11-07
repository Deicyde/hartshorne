---
article_id: af_1f79dc57d1611e08e4dcdb41
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Ringed.moduleSheafHomPrecomp Hartshorne.Ringed.sheafExtPrecomp Hartshorne.Ringed.sheafExtContraδ Hartshorne.Ringed.sheafHomContraδ Hartshorne.Ringed.sheafHom_contra_mono Hartshorne.Ringed.sheafHom_contra_exact₂ Hartshorne.Ringed.sheafHom_contra_exact₃ Hartshorne.Ringed.sheafHom_contra_exact₁ Hartshorne.Ringed.sheafExt_contra_exact₂ Hartshorne.Ringed.sheafExt_contra_exact₃ Hartshorne.Ringed.sheafExt_contra_exact₁ Hartshorne.Ringed.sheafHomContraδ_naturality Hartshorne.Ringed.sheafExtContraδ_naturality
---

# The contravariant long exact sequence of sheaf Ext

For a short exact sequence $0 \longrightarrow F' \longrightarrow F \longrightarrow F'' \longrightarrow 0$ and an $\mathcal{O}_X$-module
$G$, the sheaves $\mathcal{E}xt^i_X(-,G)$ form the natural contravariant long exact
sequence beginning

$0 \longrightarrow \mathcal{H}om(F'',G) \longrightarrow \mathcal{H}om(F,G) \longrightarrow \mathcal{H}om(F',G) \longrightarrow \mathcal{E}xt^1(F'',G) \longrightarrow \cdots$.

## Depends on

- [Sheaf Ext](sheaf-ext.md)

## Proof depends on

- [Injectives restrict to open subsets](open-restriction-injective.md)
- [Sheaf Hom as a left-exact functor](module-sheaf-hom-left-exact.md)
- Exactness of $\mathcal{H}om_X(-,J)$ for an injective module sheaf $J$.

## Sources

- [Hartshorne III.6, Proposition 6.4, printed p.234](../../../../sources/hartshorne-iii-6.md#exact-sequences-and-locally-free-resolutions-printed-pp234235)
