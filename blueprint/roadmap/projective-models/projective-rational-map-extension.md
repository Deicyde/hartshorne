---
article_id: af_80c5665b10ceeb3789f03554
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.DominantRatMap.existsUnique_projectiveCurve_extension
---

# Extension of dominant rational maps

Every dominant rational map from a nonsingular projective curve to a
projective variety extends to a unique morphism; when the target is a curve,
the extension is dominant.  The sole main declaration is planned as
`Hartshorne.DominantRatMap.existsUnique_projectiveCurve_extension`.

Choose a nonempty representative domain for the rational map and apply the
open-domain form of Proposition 6.8.  Uniqueness is independent of the
representative by Lemma 4.1, so this construction respects rational-map
equivalence and gives the full-faithfulness step in Corollary 6.12.

## Depends on

- [The three curve categories](curve-categories.md)
- [Rational maps](../rational-maps/rational-map.md)
- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)

## Proof depends on

- [Extension to a projective target](projective-extension.md)
- [Morphisms agreeing on an open set](../rational-maps/morphism-agreement.md)
- [Nonsingular curves are open subcurves of their valuation spaces](../curve-normalization/curve-to-valuation-space-iso.md)

## Sources

- [Hartshorne I.6, proof of Corollary 6.12 (pp. 45--46)](../../sources/hartshorne.md#i6-projective-models)
