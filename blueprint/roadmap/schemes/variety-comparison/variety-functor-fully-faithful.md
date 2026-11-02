---
article_id: af_a896c68bfa7d7ac69130a777
declaration: theorem
origin: cited
---

# The variety-to-scheme functor is fully faithful

For varieties $V,W$ over an algebraically closed field $k$, the natural map

$\operatorname{Hom}_{\mathrm{Var}_k}(V,W)\longrightarrow\operatorname{Hom}_{\mathrm{Sch}_k}(t(V),t(W))$

is bijective.

Faithfulness follows by restriction to classical closed points.  For fullness,
a morphism of schemes over $k$ preserves $k$-rational closed points by its induced
residue-field maps, hence restricts to a continuous map $V \to W$; its sheaf map
says precisely that regular functions pull back to regular functions.  The
generic-completion construction then recovers the original scheme morphism.
This is Hartshorne's Exercise II.2.15(b,c) and completes Proposition II.2.6.

## Depends on

- [The variety-to-scheme functor](variety-to-scheme-functor.md)
- [Classical points are the closed points](variety-closed-points.md)
- [Restricting the structure sheaf recovers regular functions](variety-restricted-sheaf.md)

## Sources

- [Hartshorne II.2, Proposition 2.6 and Exercise 2.15(b),(c) (pp. 78–81)](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)
