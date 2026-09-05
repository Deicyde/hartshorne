/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ChartIdeal
import Hartshorne.Projective.QuotientGrading
import Hartshorne.Affine.CoordinateRing

/-!
# Dehomogenising descends to the coordinate rings

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(b) and (c).

`α` carries `J(Y)` into `I(Yᵢ)`, so it descends to a ring map
`S(Y) → A(Yᵢ)`. This is the map whose localisation at `xᵢ` is the isomorphism
`S(Y)_(xᵢ) ≅ A(Yᵢ)` that Theorem 3.4 runs on.

The containment is the easy direction of the ideal dictionary. A generator of
`J(Y)` is homogeneous and vanishes on `Y`, so `xᵢ · g` lies in `J(Y)` too, which
is exactly the condition for `α(g)` to lie in `I(Yᵢ)`.

Note the asymmetry: `α` maps `J(Y)` into `I(Yᵢ)` but not onto it, and the
descended map is neither injective nor surjective in general. Both defects are
repaired by inverting `xᵢ`, which is why Theorem 3.4 is stated for the
localisation.

## Main definitions

* `Hartshorne.coordChartHom`

## Main results

* `Hartshorne.dehomogenize_map_le`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- `α` carries `J(Y)` into `I(Yᵢ)`. -/
theorem dehomogenize_map_le (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    Ideal.map (dehomogenize i) (homogeneousVanishingIdeal Y)
      ≤ vanishingIdeal k (chartMap i '' (Y ∩ standardChart i)) := by
  rw [homogeneousVanishingIdeal, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨g, hgmem, rfl⟩
  obtain ⟨⟨n, hg⟩, hvan⟩ := hgmem
  refine (dehomogenize_mem_vanishingIdeal_iff hg Y).2 ?_
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨n, hg⟩, hvan⟩)

/-- The map `S(Y) → A(Yᵢ)` induced by dehomogenisation. -/
noncomputable def coordChartHom (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    homogeneousCoordinateRing Y →+*
      coordinateRing (chartMap i '' (Y ∩ standardChart i)) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (dehomogenize i).toRingHom)
    fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact dehomogenize_map_le i Y (Ideal.mem_map_of_mem _ ha)

@[simp]
theorem coordChartHom_mk (i : σ) (Y : Set (ProjectiveSpace k σ)) (g : MvPolynomial σ k) :
    coordChartHom i Y (Ideal.Quotient.mk _ g)
      = Ideal.Quotient.mk _ (dehomogenize i g) :=
  rfl

end Hartshorne
