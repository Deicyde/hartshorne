---
article_id: af_fee62ec99afff5f65d12af06
declaration: exact sequence
origin: cited
lean: Hartshorne.structureSheafModule Hartshorne.normalizationPushforward Hartshorne.normalizationUnitMap Hartshorne.normalizationDeltaQuotient Hartshorne.normalizationDeltaSequence Hartshorne.normalizationDeltaSequence_shortExact Hartshorne.isCoherent_normalizationPushforward Hartshorne.isCoherent_normalizationDeltaQuotient Hartshorne.semilocalIntegralClosure Hartshorne.normalizationDefectModule Hartshorne.normalizationPushforwardStalkEquiv Hartshorne.normalizationPushforwardStalkEquiv_unit Hartshorne.normalizationDeltaQuotientStalkEquiv Hartshorne.module_finite_semilocalIntegralClosure Hartshorne.finite_setOf_isMaximal_semilocalIntegralClosure Hartshorne.finite_moduleSheafSupport_normalizationDeltaQuotient Hartshorne.normalizationDelta Hartshorne.normalizationDelta_eq_length_stalk Hartshorne.normalizationDelta_ne_top Hartshorne.finite_setOf_normalizationDelta_ne_zero Hartshorne.normalizationDeltaQuotient_spec
---

# The normalization defect quotient

Let $X$ be an integral projective one-dimensional scheme over an
algebraically closed field and let $\nu:\widetilde X\to X$ be its normalization.
There is an exact sequence of coherent sheaves

$0 \to \mathcal{O}_X \to \nu _* \mathcal{O}_\widetilde{X} \to Q \to 0$,

where $Q$ has finite support and

$Q_P \simeq \widetilde{\mathcal{O}} _P / \mathcal{O}_{X,P}$.

Here $\widetilde{\mathcal{O}} _P$ is the finite semilocal integral closure of $\mathcal{O}_{X,P}$ in
$K(X)$, namely the stalk $(\nu _*\mathcal{O}_\widetilde{X})_P$. Its localizations at maximal
ideals are the normalization local rings above $P$; it is not replaced by
their product. Define $\delta _P$ as the finite module length of this quotient;
only finitely many $\delta _P$ are nonzero.

## Depends on

- [Normalization](../../schemes/normalization-and-exercises/normalization-construction.md)
- [Normalization is finite over a finite-type field scheme](../../schemes/normalization-and-exercises/normalization-finite-type-field.md)
- [Finite pushforward preserves coherence](../../schemes/modules-and-quasicoherent/finite-pushforward-coherent.md)
- [Sections with support of a quasicoherent sheaf](../../schemes/coherent-sheaves/sections-with-support-quasicoherent.md)
- [Support of a quasi-coherent module](../../schemes/coherent-sheaves/module-sheaf-support.md)

## Proof depends on

- Normalization is an isomorphism over the normal locus, whose complement on
  a Noetherian integral curve is a finite set of closed points.
- On an affine neighbourhood of $P$, finite pushforward is restriction of
  scalars; localizing that finite algebra at $P$ gives the semilocal integral
  closure whose maximal localizations are the normalization local rings above
  $P$.
- [Abelian closure of quasi-coherent sheaves](../../schemes/modules-and-quasicoherent/quasicoherent-abelian-closure.md)

## Sources

- [Hartshorne IV.1, Exercise 1.8 preamble, p.298](../../../sources/hartshorne-iv-1.md#exercise-disposition-printed-pp297298)
