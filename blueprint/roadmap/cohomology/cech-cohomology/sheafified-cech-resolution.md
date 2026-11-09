---
article_id: af_129a7a2a84a9a482e9669070
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.SheafifiedCech.augmentedSheafifiedCechComplex_exactAt Hartshorne.SheafifiedCech.globalSectionsIso Hartshorne.SheafifiedCech.cochainSheaf Hartshorne.SheafifiedCech.cochainSheafIsProduct Hartshorne.SheafifiedCech.sheafifiedCechComplex Hartshorne.SheafifiedCech.augmentation Hartshorne.SheafifiedCech.augmentedSheafifiedCechComplex Hartshorne.SheafifiedCech.sheafifiedCechComplexFunctor Hartshorne.SheafifiedCech.augmentationNatTrans Hartshorne.SheafifiedCech.augmentation_naturality Hartshorne.SheafifiedCech.quasiIso_augmentationHom Hartshorne.SheafifiedCech.globalSectionsNatIso Hartshorne.SheafifiedCech.augmentedSheafifiedCechComplexFunctor
---

# The sheafified Čech resolution

For an open cover $U$ and abelian sheaf $F$, let the degree-$p$ term
$\mathcal{C}^p(U,F)$ be the product, over increasing tuples, of the direct
image of $F$ restricted to the corresponding intersection, with the Čech
differential. Then $\mathcal{C}^\bullet(U,F)$ is a resolution of $F$: there is
a natural map $\varepsilon\colon F\to\mathcal{C}^0(U,F)$ such that

$0\longrightarrow F\overset{\varepsilon}{\longrightarrow}\mathcal{C}^0(U,F)\longrightarrow\mathcal{C}^1(U,F)\longrightarrow\cdots$

is exact. The complex $\mathcal{C}^\bullet(U,F)$ and $\varepsilon$ are natural
in $F$, and $\Gamma(X,\mathcal{C}^p(U,F))=C^p(U,F)$ naturally in $F$, so the
global sections of $\mathcal{C}^\bullet(U,F)$ form the ordered Čech complex.

## Depends on

- [The ordered Čech complex](open-cover-cech-complex.md)
- [Direct image of a sheaf](../../schemes/sheaf-functors/direct-image.md)
- [Restriction and stalks](../../schemes/sheaf-functors/restriction-stalk.md)

## Proof depends on

- [Exactness is detected on stalks](../../schemes/sheaves/stalkwise-exactness.md)
- Inserting a cover index containing the point defines a contracting
  homotopy on the stalk complex.

## Sources

- [Hartshorne III, Lemma 4.2 (pp.220–221)](../../../sources/hartshorne-iii-3-4.md#cech-construction-and-comparison)
