---
article_id: af_4ff6678fe30f65e86a6bb8b4
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.isIso_absoluteNormalizationMap_restrict_of_isNormal
---

# The normalization is an isomorphism over a normal open

Let $X$ be an integral scheme with normalization $\nu : \widetilde{X} \to X$, and let
$U \subseteq X$ be an open subset that is a normal scheme. Then $\nu$ restricts to an
isomorphism $\nu^{-1}(U) \to U$.

Over an affine open $\operatorname{Spec} A \subseteq U$ the ring $A$ is an integrally
closed domain with fraction field $K(X)$, so its integral closure in $K(X)$ is $A$
itself and the chart of $\widetilde{X}$ over $\operatorname{Spec} A$ maps
isomorphically onto it. These affine opens cover $U$, and being an isomorphism
is local on the target.

This bridge is not stated by Hartshorne. It is the step behind his requirement
in Exercise III.5.8(b) that the chosen points of the normalization lie over
nonsingular points: on an integral curve over a field the nonsingular points
are normal.

## Depends on

- [Construction of the normalization](normalization-construction.md)
- [Normal schemes](normal-scheme.md)

## Proof depends on

- [Affine opens have fraction field $K(X)$](function-field-integral-scheme.md)

## Sources

- [Hartshorne II.3, Exercise 3.8 (p. 91)](../../../sources/hartshorne-ii-3.md#later-used-exercises)
- [Its use in Hartshorne III, Exercise 5.8(b) (p.232)](../../../sources/hartshorne-iii-5.md#adopted-exercises-pp230233)
