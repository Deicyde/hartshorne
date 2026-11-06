---
article_id: af_600dcf83ce173a433697ccd1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.SatisfiesConditionStar.affineLine AlgebraicGeometry.Scheme.affineLinePullback AlgebraicGeometry.Scheme.affineLineClassGroupHom AlgebraicGeometry.Scheme.affineLineClassGroupHom_bijective AlgebraicGeometry.Scheme.affineLineClassGroupEquiv AlgebraicGeometry.Scheme.affineLineClassGroupEquiv_weilDivisorClassHom
---

# Affine-line invariance of the class group

If $X$ satisfies $(\cdot )$, then its relative affine line
$X \times \operatorname{Spec} Z[t]$ also satisfies $(\cdot )$, and pullback along the projection
induces an isomorphism
$Cl X \cong Cl(X \times A^1)$.

Distinguish vertical codimension-one points pulled back from $X$ from
horizontal points over the generic point. A horizontal prime becomes
principal over $K(X)[t]$, which proves surjectivity; comparison of horizontal
components of a principal divisor proves injectivity.

## Depends on

- [Codimension-one stalks are DVRs](codimension-one-stalk-dvr.md)
- [Linear equivalence and the Weil class group](weil-linear-equivalence.md)

## Proof depends on

- Classification of height-one primes after base change to $K(X)[t]$.
- Polynomial rings over fields are principal ideal domains in one variable.

## Sources

- [Hartshorne II.6, Proposition 6.6 on printed pp.134–135](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
