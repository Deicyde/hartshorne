---
article_id: af_a5dfc40192ea62ea4180e6e2
declaration: theorem
origin: cited
lean: Hartshorne.ProjectiveClosedSubscheme.saturation Hartshorne.ProjectiveClosedSubscheme.saturation_isHomogeneous Hartshorne.ProjectiveClosedSubscheme.le_saturation Hartshorne.ProjectiveClosedSubscheme.ker_projQuotientι_eq_iff Hartshorne.ProjectiveClosedSubscheme.ker_projQuotientι_le_iff Hartshorne.ProjectiveClosedSubscheme.saturation_gammaStarIdeal Hartshorne.ProjectiveClosedSubscheme.isGreatest_gammaStarIdeal Hartshorne.ProjectiveClosedSubscheme.le_gammaStarIdeal_of_ker_eq Hartshorne.ProjectiveClosedSubscheme.gammaStarIdeal_ker_projQuotientι
statement: formalized
proof: formalized
---

# Saturation of projective ideals

For a homogeneous ideal $I \subseteq S = A[x_{0},\ldots ,x_{r}]$, define its saturation by

$I^{\mathrm{sat}}=\{s\in S\mid\forall i\in\{0,\ldots,r\},\;\exists n\in\mathbb N,\;x_i^n s\in I\}$.

This is a homogeneous ideal; two homogeneous ideals define the same closed
subscheme of projective space exactly when their saturations agree; and for a
closed subscheme $Y$, $\Gamma _*(I_Y)$ is saturated and is the largest homogeneous
ideal defining $Y$.

## Depends on

- [Homogeneous ideals define projective closed subschemes](projective-closed-subscheme-homogeneous-ideal.md)

## Proof depends on

- [The sheaf of a graded module on Proj](proj-graded-module-sheaf.md)
- Compare the localized ideals on every standard chart $D_{+}(x_i)$; equality
  there is exactly the quantified power condition above.

## Sources

- [Hartshorne II.5, Exercise 5.10(a–c) (p.125)](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
