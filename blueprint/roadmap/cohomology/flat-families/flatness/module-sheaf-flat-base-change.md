---
article_id: af_e6fc97faaa85552c7406c057
declaration: theorem
origin: cited
---

# Base change of a module sheaf flat over a base

Let $f : X \to Y$, let $F$ be an $\mathcal{O}_X$-module flat over $Y$, and let
$g : Y' \to Y$ be any scheme morphism. For $X'=X \times _Y Y'$ with projection
$f' : X' \to Y'$, the module pullback of $F$ to $X'$ is flat over $Y'$.

## Depends on

- [A module sheaf flat over a base](module-sheaf-flat-over-base.md)
- [Pushforward, pullback, and their adjunction](../../../schemes/modules-and-quasicoherent/module-push-pull-adjunction.md)
- [Schemes have fibre products](../../../schemes/fiber-products/schemes-have-fiber-products.md)

## Proof depends on

- [Flat modules remain flat after base change](flat-module-base-change.md)
- [Stalks of the pullback of a module sheaf](../../../schemes/module-stalks/module-pullback-stalk.md)
- [Local rings of a fibre product](../../../schemes/fiber-products/fiber-product-local-ring.md)
- If $C$ is a flat $R$-algebra and $N$ is an $R$-module that is flat over a ring $B' \to R$, then $C \otimes_R N$ is flat over $B'$. Apply it with $R = \mathcal{O}_{X,x} \otimes_{\mathcal{O}_{Y,y}} \mathcal{O}_{Y',y'}$, $C = \mathcal{O}_{X',x'}$ and $N = \mathcal{O}_{Y',y'} \otimes_{\mathcal{O}_{Y,y}} F_x$, using $C \otimes_{\mathcal{O}_{X,x}} F_x \cong C \otimes_R N$.

## Sources

- [Hartshorne III.9, Proposition 9.2(b), p.254](../../../../sources/hartshorne-iii-9.md#flat-modules-and-flat-morphisms-pp253255)
