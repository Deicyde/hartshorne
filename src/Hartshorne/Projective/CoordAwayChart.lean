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
    (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i)) ∈ projCoordGrading Y 1 :=
  ⟨X i, X_mem_homogeneousSubmodule i, rfl⟩

/-- Dehomogenisation inverts the class of `xᵢ`, so it factors through the
localisation. -/
noncomputable def awayCoordChart (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    Localization.Away (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i)) →+*
      coordinateRing (chartMap i '' (Y ∩ standardChart i)) :=
  IsLocalization.lift
    (M := Submonoid.powers (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i)))
    (g := coordChartHom i Y) (by
      rintro ⟨y, n, rfl⟩
      simp)

@[simp]
theorem awayCoordChart_mk (i : σ) (Y : Set (ProjectiveSpace k σ))
    (a : homogeneousCoordinateRing Y) (n : ℕ)
    (h : (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i)) ^ n
      ∈ Submonoid.powers (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i))) :
    awayCoordChart i Y (Localization.mk a ⟨_, h⟩) = coordChartHom i Y a := by
  rw [Localization.mk_eq_mk', awayCoordChart, IsLocalization.lift_mk'_spec]
  simp

/-
The remaining step is `S(Y)_(xᵢ) ≅ A(Yᵢ)`, and it is blocked on instance
resolution rather than on mathematics.

`HomogeneousLocalization.Away (projCoordGrading Y) z` needs a `CommRing`, which
needs `GradedRing (projCoordGrading Y)`. That instance exists — it is
`instGradedAlgebraQuotGrading` — and is found for a generic homogeneous ideal,
but not for this one: the grading lives on `MvPolynomial σ k ⧸ I.toIdeal` while
the element `z` is written in `MvPolynomial σ k ⧸ homogeneousVanishingIdeal Y`.
The two are definitionally equal and unify when elaborating the *statement*, but
instance search does not see through the projection, and making
`projVanishingIdeal` reducible was not enough.

Everything else is in hand: `awayCoordChart` above is the map, surjectivity is
`dehomogenize_homogenize` modulo `I(Yᵢ)`, and injectivity is
`dehomogenize_mem_vanishingIdeal_iff` in the direction that gives a single power
of `xᵢ`.
-/

end Hartshorne
