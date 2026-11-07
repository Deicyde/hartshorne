---
article_id: af_0a0b46fa1c07ad0c16df634e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.planeCurve_tangentLine_morphism Hartshorne.planeCurveRegularLocus Hartshorne.isQuasiProjVariety_planeCurveRegularLocus Hartshorne.planeCurveTangentLine Hartshorne.planeDualCurve Hartshorne.isProjVariety_planeCurve
---

# The tangent morphism and dual plane curve

Let $Y$ be a projective plane curve. For every regular point $P \text{of} Y$, there
is a unique line $T_P(Y)$ whose local intersection multiplicity with $Y$ at
$P$ is greater than one. The assignment

$P\mapsto T_P(Y)$

is a morphism from the regular locus of $Y$ to the dual projective plane.
Define the dual curve $Y^*$ as the closure of its image.

## Depends on

- [Local intersection multiplicity of plane curves](local-plane-curve-intersection-multiplicity.md)
- [Regular points and nonsingular schemes](../../schemes/differentials/scheme-differentials/regular-points-and-nonsingular-schemes.md)
- [Intrinsic nonsingularity](../../nonsingular-varieties/intrinsic-nonsingularity.md)
- [Morphisms](../../morphisms/morphism.md)

## Proof depends on

- On an affine chart, the tangent line is given by the first derivatives of a
  local equation; these homogeneous coordinates glue to the Gauss morphism.
- [An irreducible polynomial has a nonzero partial derivative](../../nonsingular-varieties/irreducible-polynomial-nonzero-partial.md)

## Sources

- [Hartshorne I.7, Exercise 7.3, p.54](../../../sources/hartshorne.md#i7-adopted-dual-curve-exercise)
