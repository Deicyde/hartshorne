---
declaration: homomorphism
origin: cited
source_units: [appendix-a-sections-1-2]
---

# Pullback by the graph construction

Within an intersection theory, define pullback along `f:X->X'` by

`f^*([Y'])=p1_*(Gamma_f . [p2^(-1)(Y')])`,

where `Gamma_f` is the graph cycle in `X times X'`. Here the inverse image is
the flat product cycle `X times Y'`, not an invocation of the pullback being
defined. The final raw pushforward is supported on the graph, where the first
projection is an isomorphism.

The second projection is essential: `p1^(-1)(Y')` is ill-typed for
`Y' subset X'`.

## Depends on

- [The intersection-theory axiom interface](intersection-theory-axiom-api.md)
- [External products of cycles](external-product-of-cycles.md)
- [Graphs of morphisms into separated schemes](../../../schemes/separated-morphisms/separated-morphism.md)
- [Raw pushforward of cycles](../cycles/raw-cycle-pushforward.md)

## Sources

- [Hartshorne Appendix A.1, graph definition of pullback, p.426](../../../../sources/hartshorne-appendix-a-1-2.md)
