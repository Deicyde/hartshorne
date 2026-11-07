---
article_id: af_cefd5671b7a80410e671151c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Koszul.isZero_sequenceKoszulComplex_homology_of_isWeaklyRegular Hartshorne.Koszul.quasiIso_sequenceKoszulAugmentation Hartshorne.Koszul.sequenceKoszulAugmentation
---

# A regular sequence gives a Koszul resolution

If $f_{1},\ldots ,f_{r}$ is a regular sequence on an $A$-module $M$, then

$H_p(K(f;M))=0$ for $p>0$

and the augmentation induces
$H_{0}(K(f;M))\simeq M/(f_{1},\ldots ,f_{r})M$.

## Depends on

- [The Koszul complex](koszul-complex.md)
- [Regular sequences and Cohen–Macaulay quotients](../../../schemes/differentials/local-complete-intersections/cohen-macaulay-regular-sequence-quotient.md)

## Proof depends on

- Induction on the regular sequence via the tensor-product description of
  the next one-element Koszul complex.

## Sources

- [Hartshorne III.7, Proposition 7.10A, p.245](../../../../sources/hartshorne-iii-7.md#koszul-calculation-and-the-canonical-sheaf-pp245247)
- [Stacks Project, Section 15.31, tag 062D](https://stacks.math.columbia.edu/tag/062D)
- Matsumura, *Commutative Algebra*, Theorem 43, p.135
