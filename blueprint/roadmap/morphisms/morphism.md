---
article_id: af_300dd006c62e894e27ba7e7b
declaration: structure
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.VarietyHom
---

# Morphisms

A *morphism* $\varphi : X \to Y$ of varieties is a continuous map such that for every
open $V \subseteq Y$ and every regular $f : V \to k$, the composite $f \circ \varphi$ is regular on
$\varphi ^{-1}(V)$. Composition of morphisms is a morphism, so varieties over $k$ form a
category. An *isomorphism* is a morphism admitting a two-sided inverse morphism.

An isomorphism is bijective and bicontinuous, but a bijective bicontinuous
morphism need not be an isomorphism: its inverse must also be a morphism.
Hartshorne's Exercise 3.2 gives two counterexamples, $t \mapsto (t^{2}, t^{3})$ onto the
cusp $y^{2} = x^{3}$, and the Frobenius map $t \mapsto t^{p}$ in characteristic $p$.

## Depends on

- [Varieties](variety.md)

## Sources

- [Hartshorne I.3, definition of morphism and isomorphism, with Exercise 3.2 (pp. 15-16, 21)](../../sources/hartshorne.md#i3)
