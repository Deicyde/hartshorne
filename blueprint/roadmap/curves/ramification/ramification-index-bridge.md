---
article_id: af_0f89cc90cfd9d4cd30651fa5
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.IsNonsingularCurve.ramificationIndex AlgebraicGeometry.Scheme.IsNonsingularCurve.ramificationIndex_eq AlgebraicGeometry.Scheme.IsNonsingularCurve.finiteCurvePointPullback_apply_self AlgebraicGeometry.Scheme.IsNonsingularCurve.ramificationIndex_eq_ramificationIdx' AlgebraicGeometry.Scheme.IsNonsingularCurve.ramificationIndex_eq_one_iff AlgebraicGeometry.Scheme.IsNonsingularCurve.IsTamelyRamifiedAt AlgebraicGeometry.Scheme.IsNonsingularCurve.IsWildlyRamifiedAt Hartshorne.HartshorneUnramifiedAt
---

# The ramification-index bridge

Let $f : X \to Y$ be a finite morphism of curves, let $P \in X$, and put
$Q=f(P)$. For a uniformizer $t$ of the DVR $\mathcal{O}_{(Y,Q)}$, define

$e_P=v_P(f^\#t)$.

The value $e_P$ is independent of $t$. It equals the coefficient of $P$ in
$f^*Q$ and the ideal-theoretic ramification index for the induced extension
of discrete valuation rings. Moreover, $e_P=1$ exactly when $f$ is
unramified at $P$.
Ramification is tame in characteristic zero, or in characteristic $p$ when
$p$ does not divide $e_P$; otherwise it is wild.

## Depends on

- [Nonsingular curve local rings are DVRs](../../nonsingular-curves/nonsingular-curve-local-ring-dvr.md)
- [Pullback of divisors along finite curve morphisms](../../schemes/divisors/curve-divisors/finite-curve-divisor-pullback.md)
- [Étale, flat-unramified, and differential criteria](../../cohomology/smooth-morphisms/criteria/etale-flat-unramified-equivalences.md)

## Proof depends on

- Uniformizers differ by units and local ring maps preserve units.
- The ideal-theoretic ramification index for the corresponding prime ideals
  in affine discrete-valuation neighbourhoods.

## Sources

- [Hartshorne IV.2, ramification definitions, p.299](../../../sources/hartshorne-iv-2.md#finite-maps-ramification-and-the-different-pp299301)
