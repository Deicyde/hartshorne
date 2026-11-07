---
article_id: af_3e334e4ca1d4ca1c50ba6dba
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.sectionDualMap Hartshorne.sectionDualMap_app Hartshorne.sectionDualImage Hartshorne.sectionDualImageι Hartshorne.sectionZeroIdeal Hartshorne.sectionZeroScheme Hartshorne.sectionZeroSchemeι Hartshorne.mem_sectionZeroIdeal_iff Hartshorne.sectionZeroIdeal_ideal_eq_range_sectionDualImageι Hartshorne.ker_sectionZeroSchemeι Hartshorne.ker_sectionZeroSchemeι_app Hartshorne.sectionZeroSchemeι_app_surjective Hartshorne.sectionZeroCycle
---

# The zero scheme of a section of a locally free sheaf

For a section $s \in \Gamma (X,E)$ of a locally free sheaf, let
$s^\vee :E^\vee \to \mathcal{O}_X$ be the dual map.  Define its zero scheme $Z(s)$ by the
ideal sheaf $\operatorname{image} (s^\vee )$, equivalently by the right-exact sequence

$E^\vee \to \mathcal{O}_X \to \mathcal{O}_{(Z(s))} \to 0$.

This is a scheme-theoretic zero locus.  Its associated cycle uses the generic
local lengths of its irreducible components and is not replaced by the
reduced vanishing set.

## Depends on

- [Closed subschemes and ideal data](../../schemes/coherent-sheaves/closed-subschemes-ideal-data.md)
- [Finite locally free duality](../../schemes/modules-and-quasicoherent/finite-locally-free-duality.md)
- [Fundamental cycle of a closed subscheme](../chow/cycles/closed-subscheme-fundamental-cycle.md)

## Sources

- [Hartshorne Appendix A §3, zero-scheme definition in C6, p.431](../../../sources/hartshorne-appendix-a-3.md)
