---
article_id: af_4a47c5077a5ceb83f9e2d0ba
declaration: def
origin: cited
statement: formalized
lean: AlgebraicGeometry.Scheme.Modules.FlatOverAt AlgebraicGeometry.Scheme.Modules.FlatOver
---

# A module sheaf flat over a base

For $f : X \to Y$, an $\mathcal{O}_X$-module $F$ is flat over $Y$ at $x \in X$ when
$F_x$ is flat as an $\mathcal{O}_{Y,f(x)}$-module through the stalk map of $f$. It is
flat over $Y$ when this holds at every point.

Taking $F=\mathcal{O}_X$ recovers flatness of the morphism $f$.

## Depends on

- [Sheaves of modules](../../../schemes/modules-and-quasicoherent/sheaves-of-modules.md)
- [Stalks and germs](../../../schemes/sheaves/stalks-and-germs.md)

## Proof depends on

- Restriction of scalars along the local-ring map on stalks.

## Sources

- [Hartshorne III.9, definition on p.254](../../../../sources/hartshorne-iii-9.md#flat-modules-and-flat-morphisms-pp253255)
