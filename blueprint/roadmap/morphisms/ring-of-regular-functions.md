---
article_id: af_93d17cf8e41f0ee7a7cf9564
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.globalRegular Hartshorne.VarietyHom.pullback
---

# The ring of regular functions

For a variety $Y$, the ring $\mathcal O(Y)$ of regular functions $Y\to k$
is a $k$-algebra under pointwise operations. A morphism $\varphi:X\to Y$
induces pullback

$$\varphi^*:\mathcal O(Y)\longrightarrow\mathcal O(X),\qquad
f\longmapsto f\circ\varphi.$$

Pullback respects identity and reverses composition. An isomorphism of
varieties therefore induces an isomorphism of their regular-function
algebras, making $\mathcal O(Y)$ an invariant of the variety.

## Depends on

- [Varieties](variety.md)
- [Morphisms](morphism.md)

## Sources

- [Hartshorne I.3, definition of $\mathcal{O} (Y)$ (p. 16)](../../sources/hartshorne.md#i3)
