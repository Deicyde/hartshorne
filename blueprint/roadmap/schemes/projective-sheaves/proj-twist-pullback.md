---
article_id: af_0a85053c2012b17661490eb8
declaration: isomorphism
origin: cited
source_units: [chapter-ii-section-5]
---

# Pullback of twisting sheaves

Let `S → T` preserve degrees, with both rings generated in degree one, and
let `f : U → Proj S` be the induced morphism from an open `U ⊆ Proj T`.
Then

`f^* O_{Proj S}(n) ≅ O_{Proj T}(n)|_U`,

and the direct image satisfies

`f_*(O_{Proj T}(n)|_U) ≅ (f_*O_U)(n)`,

where the twist on the right uses the `O_{Proj S}`-module structure of
`f_*O_U`. This is a pushforward formula; it is not a claim that arbitrary
module twists commute with pullback.

## Depends on

- [Twists and graded shifts](proj-twist-compatibility.md)
- [The Proj construction is functorial](../projective-spectrum/proj-partial-map.md)
- [Pushforward, pullback, and their adjunction](../modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- The affine extension- and restriction-of-scalars formulas on each standard
  chart.

## Sources

- [Hartshorne II.5, Proposition 5.12(c) (p.117)](../../../sources/hartshorne-ii-5.md#graded-modules-twists-and-reconstruction-on-proj)
