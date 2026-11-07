---
article_id: af_98097ebb6a196e47a684358a
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Koszul.contraction Hartshorne.Koszul.contraction_contraction Hartshorne.Koszul.contraction_ιMulti Hartshorne.Koszul.koszulComplex Hartshorne.Koszul.koszulComplex_d_tmul_ιMulti Hartshorne.Koszul.koszulForm Hartshorne.Koszul.sequenceKoszulComplex Hartshorne.Koszul.sequenceKoszulComplex_d_basis Hartshorne.Koszul.koszulAugmentation Hartshorne.Koszul.koszulAugmentationIsCokernel Hartshorne.Koszul.koszulHomologyZeroIso Hartshorne.Koszul.sequenceKoszulHomologyZeroIso Hartshorne.Koszul.koszulFunctor Hartshorne.Koszul.koszulMap_f_zero_comp_koszulAugmentation Hartshorne.Koszul.baseChangeComplex Hartshorne.Koszul.exteriorPowerBaseChangeEquiv Hartshorne.Koszul.koszulBaseChangeIso Hartshorne.Koszul.sequenceKoszulBaseChangeIso Hartshorne.Koszul.sequenceKoszulLocalizationIso Hartshorne.Koszul.koszulChangeOfBasis Hartshorne.Koszul.koszulChangeOfBasis_comp Hartshorne.Koszul.koszulChangeOfBasis_naturality Hartshorne.Koszul.koszulChangeOfBasisIso Hartshorne.Koszul.sequenceKoszulChangeOfBasis Hartshorne.Koszul.sequenceKoszulChangeOfBasisIso
---

# The Koszul complex

For a commutative ring $A$, an $A$-module $M$, and a finite sequence
$f_{1},\ldots ,f_{r}$, define the homological Koszul complex

$K_p(f;M)=\bigwedge ^p(A^r)\otimes _A M$

with the alternating contraction differential. Include its augmentation to
$M/(f_{1},\ldots ,f_{r})M$, functoriality in $M$, localization, and change-of-basis
maps. These operations are compatible with the complex construction.

## Depends on

- Nothing in this roadmap.

## Proof depends on

- The alternating-sign calculation proving $d^{2}=0$.

## Sources

- [Hartshorne III.7, Koszul-complex definition, p.245](../../../../sources/hartshorne-iii-7.md#koszul-calculation-and-the-canonical-sheaf-pp245247)
- [Stacks Project, Section 15.29, tag 0621](https://stacks.math.columbia.edu/tag/0621)
