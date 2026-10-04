---
article_id: af_9dca473fa700d719aa39e1c5
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
---

# The local-to-global Ext spectral sequence

For `O_X`-modules `F,G`, take the derived-category inputs
`K=F[0]` and `L=G[0]`. Here `K` is bounded above and `L` is bounded below, so
tag 0BQP's favorable convergence hypothesis holds. Construct the natural
first-quadrant cohomological spectral sequence

`E₂^{p,q} = H^p(X,𝓔xt^q_X(F,G)) ⇒ Ext^{p+q}_X(F,G)`

with convergence to global Ext in total degree `p+q`. For every `q`, its
total-degree-`q` edge morphism

`Ext^q_X(F,G) ⟶ E₂^{0,q}=Γ(X,𝓔xt^q_X(F,G))`

agrees with the separately constructed global-to-sheaf Ext map. The source's
derived internal Hom used to construct the spectral sequence is comparison
data; it is not inferred definitionally from Mathlib's global Ext API.

## Depends on

- [Global Ext groups](global-ext-groups.md)
- [Global Ext from an injective resolution](global-ext-injective-resolution.md)
- [Sheaf Ext](../sheaf-ext/sheaf-ext.md)

## Proof depends on

- [The global-to-sheaf Ext map](global-to-sheaf-ext-map.md)
- [Module and abelian-sheaf cohomology agree](../../sheaf-cohomology/module-cohomology-comparison.md)
- Identify the cohomology sheaves of the internal derived Hom for
  `K=F[0]`, `L=G[0]` with the chosen sheaf-Ext model.

## Sources

- [Hartshorne III.6, Remark 6.9.1, printed p.236](../../../../sources/hartshorne-iii-6.md#tensor-stalk-and-projective-comparison-printed-pp235236)
- [Stacks Project, tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
