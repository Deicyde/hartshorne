---
article_id: af_5b2f2abbc298a5bf3bfb5336
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.moduleSheafSupport Hartshorne.moduleSheafSupport_tilde Hartshorne.moduleSheafSupport_tilde_eq_zeroLocus Hartshorne.isClosed_moduleSheafSupport_of_isCoherent Hartshorne.sectionSupport_tilde_toOpen_top
---

# Support of a quasi-coherent module

For a sheaf of $\mathcal{O}_X$-modules $F$, define

$$\operatorname{Supp}(F)=\{x\in X\mid F_x\ne 0\}.$$

If $X=\operatorname{Spec}A$ and $F=\widetilde M$, this is the set
of primes $\mathfrak p$ for which $M_{\mathfrak p}\ne 0$. For a
finitely generated module $M$,
$\operatorname{Supp}(\widetilde M)=V(\operatorname{ann}_A M)$.
Consequently the support of a coherent sheaf on a Noetherian scheme
is closed.

This node packages the internal support lemmas needed by the adopted parts of
Exercise 5.6; parts (a)–(c) are not independently adopted targets. The
analogous formula for a single global section,
$\operatorname{Supp}(m)=V(\operatorname{ann}_A m)$, is a supporting lemma rather than another main
artifact.

## Depends on

- [Stalks of an associated affine module](../modules-and-quasicoherent/tilde-localization.md)
- [Coherent affine-local criterion](../modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [The support of sections and sheaves](../sheaf-functors/support-of-sections-and-sheaves.md)

## Proof depends on

- The description of module support by annihilators and its closedness for finitely generated modules.

## Sources

- [Hartshorne II.5, Exercise 5.6(a–c), internal support lemmas (p.124)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
