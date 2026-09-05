/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.CoordChart
import Hartshorne.Projective.AwayChart
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# `S(Y)_(xᵢ) ≅ A(Yᵢ)`

Hartshorne, *Algebraic Geometry*, I.3, the bridge Theorem 3.4(b) and (c) run on.

The homogeneous coordinate ring of `Y`, localised at `xᵢ` and cut to degree
zero, is the affine coordinate ring of the chart piece `Yᵢ`.

The proof is the ambient case with `S(Y)` and `A(Yᵢ)` in place of `S` and `k[y]`.
Dehomogenisation descends to `S(Y) → A(Yᵢ)` and sends the class of `xᵢ` to `1`,
a unit, so it factors through the localisation; the graded piece is then carried
along.

Both halves of bijectivity are the ideal dictionary. Surjectivity is
`α(β(p)) = p` again, now modulo `I(Yᵢ)`. Injectivity is the direction that has
content: if `α(g) ∈ I(Yᵢ)` then `xᵢ · g ∈ J(Y)`, so the fraction `g/xᵢⁿ` is
already zero — and with a single power of `xᵢ`, which is what makes the
localisation see it.

## Main definitions

* `Hartshorne.projVanishingIdeal`, `Hartshorne.coordAwayChartEquiv`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- `J(Y)` as a bundled homogeneous ideal, so that `S(Y)` can be graded. -/
noncomputable abbrev projVanishingIdeal (Y : Set (ProjectiveSpace k σ)) :
    HomogeneousIdeal (homogeneousSubmodule σ k) :=
  ⟨homogeneousVanishingIdeal Y, isHomogeneousIdeal_homogeneousVanishingIdeal Y⟩

/-- The grading on `S(Y)`. -/
noncomputable abbrev projCoordGrading (Y : Set (ProjectiveSpace k σ)) :
    ℕ → Submodule k (homogeneousCoordinateRing Y) :=
  quotGrading (homogeneousSubmodule σ k) (projVanishingIdeal Y)

omit [DecidableEq σ] in
/-- The class of `xᵢ` is homogeneous of degree one in `S(Y)`. -/
theorem mk_X_mem_projCoordGrading (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)) ∈ projCoordGrading Y 1 :=
  ⟨X i, X_mem_homogeneousSubmodule i, rfl⟩

/-- Dehomogenisation sends the class of `xᵢ` to `1`. -/
@[simp]
theorem coordChartHom_mk_X (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    coordChartHom i Y (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)) = 1 := by
  rw [coordChartHom_mk, dehomogenize_X_self, map_one]

/-- Dehomogenisation inverts the class of `xᵢ`, so it factors through the
localisation. -/
noncomputable def awayCoordChart (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    Localization.Away (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)) →+*
      coordinateRing (chartMap i '' (Y ∩ standardChart i)) :=
  IsLocalization.lift
    (M := Submonoid.powers (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)))
    (g := coordChartHom i Y) (by
      rintro ⟨y, n, rfl⟩
      rw [map_pow, coordChartHom_mk_X, one_pow]
      exact isUnit_one)

@[simp]
theorem awayCoordChart_mk (i : σ) (Y : Set (ProjectiveSpace k σ))
    (a : homogeneousCoordinateRing Y) (n : ℕ)
    (h : (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)) ^ n
      ∈ Submonoid.powers (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i))) :
    awayCoordChart i Y (Localization.mk a ⟨_, h⟩) = coordChartHom i Y a := by
  rw [Localization.mk_eq_mk', awayCoordChart, IsLocalization.lift_mk'_spec, map_pow,
    coordChartHom_mk_X, one_pow, one_mul]

noncomputable instance instGradedProjCoord (Y : Set (ProjectiveSpace k σ)) :
    GradedAlgebra (projCoordGrading Y) :=
  instGradedAlgebraQuotGrading _ _

/-- The map `S(Y)_(xᵢ) → A(Yᵢ)`. -/
noncomputable def coordAwayToPoly (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    HomogeneousLocalization.Away (projCoordGrading Y)
        (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)) →+*
      coordinateRing (chartMap i '' (Y ∩ standardChart i)) where
  toFun z := awayCoordChart i Y z.val
  map_one' := by simp [HomogeneousLocalization.val_one]
  map_mul' a b := by simp [HomogeneousLocalization.val_mul]
  map_zero' := by simp [HomogeneousLocalization.val_zero]
  map_add' a b := by simp [HomogeneousLocalization.val_add]

@[simp]
theorem coordAwayToPoly_mk (i : σ) (Y : Set (ProjectiveSpace k σ)) (n : ℕ)
    (a : homogeneousCoordinateRing Y) (ha : a ∈ projCoordGrading Y (n • 1)) :
    coordAwayToPoly i Y (HomogeneousLocalization.Away.mk (projCoordGrading Y)
      (mk_X_mem_projCoordGrading i Y) n a ha) = coordChartHom i Y a := by
  show awayCoordChart i Y _ = _
  rw [HomogeneousLocalization.Away.val_mk, awayCoordChart_mk]

/-
Bijectivity of `coordAwayToPoly` is the remaining step, and both arguments are
settled; what is left is Lean plumbing.

Surjectivity: `homogenize i p` is homogeneous of degree `p.totalDegree`, and
`coordAwayToPoly` sends the corresponding fraction to
`α(β(p)) = p` modulo `I(Yᵢ)`.

Injectivity: if the image of `g/xᵢⁿ` vanishes then `α(g) ∈ I(Yᵢ)`, so
`xᵢ · g ∈ J(Y)` by `dehomogenize_mem_vanishingIdeal_iff`, so the class of
`xᵢ · g` is zero in `S(Y)` and the fraction is zero — with a single power of
`xᵢ`, which is what the localisation can see.

The friction is that `rw` will not fire `HomogeneousLocalization.Away.val_mk`
against terms built here: the `GradedRing` instance inside the goal's `Away.mk`
is not syntactically the one `val_mk` elaborates with, even though both are
`instGradedProjCoord`. `val_mk` is `rfl`, so the way through is to restate the
two computation rules in this file as `rfl` lemmas in the exact spelling used,
rather than rewriting with the upstream ones.
-/

end Hartshorne
