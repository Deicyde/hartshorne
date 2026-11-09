---
article_id: af_0a85053c2012b17661490eb8
declaration: isomorphism
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ProjTwistPullback.pullbackTwistIso Hartshorne.ProjTwistPullback.pushforwardTwistIso Hartshorne.ProjTwistPullback.isIso_psiAdj Hartshorne.ProjTwistPullback.psi Hartshorne.ProjTwistPullback.psiAdj
---

# Pullback of twisting sheaves

Let $S \to T$ preserve degrees, with both rings generated in degree one, and
let $f : U \to \operatorname{Proj} S$ be the induced morphism from an open $U \subseteq \operatorname{Proj} T$.
Then

$f^* \mathcal{O}_{\operatorname{Proj} S}(n) \cong \mathcal{O}_{\operatorname{Proj} T}(n)|_U$,

and the direct image satisfies

$f_*(\mathcal{O}_{\operatorname{Proj} T}(n)|_U) \cong (f_*\mathcal{O}_U)(n)$,

where the twist on the right uses the $\mathcal{O}_{\operatorname{Proj} S}$-module structure of
$f_*\mathcal{O}_U$. This is a pushforward formula; it is not a claim that arbitrary
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
