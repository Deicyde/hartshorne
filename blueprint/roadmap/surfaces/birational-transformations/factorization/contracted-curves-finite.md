---
article_id: af_1a6475a7209b134c37f98148
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.contractedCurves Hartshorne.numContractedCurves Hartshorne.contractedCurves_finite Hartshorne.contractedCurves_finite_of_isNormal
---

# A birational morphism of smooth projective surfaces contracts finitely many curves

For a birational morphism $f:X'\to X$ of nonsingular projective surfaces, only
finitely many irreducible curves of $X'$ map to points. Define $n(f)$ to be
their number.

The nonsingularity of $X'$ is kept as in the source; it is not needed, because
the argument uses only that $X$ is normal and that $X'$ is an integral
projective surface.

## Depends on

- [The fundamental locus on a normal surface is finite](../fundamental-loci/normal-source-fundamental-locus-codimension-two.md)
- [Regular points and nonsingular schemes](../../../schemes/differentials/scheme-differentials/regular-points-and-nonsingular-schemes.md)

## Proof depends on

- [Serre's criterion for normality](../../../schemes/differentials/local-complete-intersections/serre-normality-criterion.md)
- [Regular local rings are Cohen–Macaulay](../../../schemes/differentials/local-complete-intersections/regular-local-implies-cohen-macaulay.md)
- Every contracted curve lies in the inverse image of a fundamental point of
  $f^{-1}$. There are finitely many such points, and each Noetherian fibre has
  finitely many irreducible components.

## Sources

- [Hartshorne V.5, first part of Corollary 5.4, pp.411–412](../../../../sources/hartshorne-v-5.md)
