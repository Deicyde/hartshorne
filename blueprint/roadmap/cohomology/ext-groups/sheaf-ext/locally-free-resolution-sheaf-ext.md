---
article_id: af_165cb62f9400411061e1bfca
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Ringed.sheafExtIsoHomologyOfLocallyFreeResolution Hartshorne.Ringed.moduleSheafHomComplex Hartshorne.Ringed.moduleSheafHomComplex_d Hartshorne.Ringed.moduleSheafHomFunctor_preservesHomology Hartshorne.Ringed.isZero_sheafExt_of_isFiniteLocallyFree
---

# Locally free resolutions compute sheaf Ext

Suppose $L_{\bullet} \longrightarrow F \longrightarrow 0$ is a nonnegative homological resolution, possibly
unbounded to the left, whose terms are finite-rank locally free
$\mathcal{O}_X$-modules. For every $\mathcal{O}_X$-module $G$, construct natural isomorphisms

$\mathcal{E}xt^i_X(F,G) \cong H^i(\mathcal{H}om_X(L_{\bullet} ,G))$.

Only the terms needed through degree $i+1$ enter the degree-$i$ comparison;
no finite-length resolution is assumed.

## Depends on

- [Sheaf Ext](sheaf-ext.md)
- [Duality for finite locally free sheaves](../../../schemes/modules-and-quasicoherent/finite-locally-free-duality.md)

## Proof depends on

- [The contravariant long exact sequence of sheaf Ext](sheaf-ext-contravariant-long-exact.md)
- Exactness of $\mathcal{H}om_X(L,-)$ for finite locally free $L$.

## Sources

- [Hartshorne III.6, Proposition 6.5, printed p.234](../../../../sources/hartshorne-iii-6.md#exact-sequences-and-locally-free-resolutions-printed-pp234235)
