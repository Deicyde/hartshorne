/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.RelativeDifferentialsFibreRank
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-!
# Smoothness of relative dimension `n` from smoothness and the rank of differentials

These are supporting steps towards the comparison of Hartshorne's definition of a smooth
morphism (III.10, p. 268) with the locally standard smooth predicate.

* `AlgebraicGeometry.Scheme.smoothOfRelativeDimension_iff_smooth_and_finrank_fibre`:
  `f` is smooth of relative dimension `n` if and only if `f` is smooth and every fibre
  `(Ω_{X/Y})_x ⊗ k(x)` has dimension `n`.
* `AlgebraicGeometry.Scheme.smoothOfRelativeDimension_of_flat_of_smooth_fiber`: a flat morphism
  locally of finite presentation whose scheme-theoretic fibres are smooth, and whose differential
  fibres `(Ω_{X/Y})_x ⊗ k(x)` all have dimension `n`, is smooth of relative dimension `n`.
* `AlgebraicGeometry.Scheme.smoothOfRelativeDimension_fiberToSpecResidueField`: smoothness of
  relative dimension `n` passes to the scheme-theoretic fibres.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing Module

namespace AlgebraicGeometry

open RelDiffLocal

universe u

/-- If `f` is smooth and every fibre `(Ω_{X/Y})_x ⊗ k(x)` has dimension `n`, then `f` is smooth
of relative dimension `n` (locally standard smooth of relative dimension `n`). -/
theorem Scheme.smoothOfRelativeDimension_of_smooth_of_finrank_fibre {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (n : ℕ)
    (h : ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          (Scheme.relativeDifferentials f).presheaf.stalk x) = n) :
    SmoothOfRelativeDimension n f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  refine ⟨U, hU, V, hV, hxV, e, ?_⟩
  let := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := hf
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nontrivial Γ(X, V) := Scheme.component_nontrivial X V
  have : Module.Free Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)] := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V)›
    exact P.free_kaehlerDifferential
  let b := Module.Free.chooseBasis Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)]
  let β : Hartshorne.specRestriction (Scheme.relativeDifferentials f) ⟨V, hV⟩ ≅
      SheafOfModules.free (Module.Free.ChooseBasisIndex Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)]) :=
    affineIso f ⟨V, hV⟩ ⟨U, hU⟩ e ≪≫ (tilde.functor Γ(X, V)).mapIso b.repr.toModuleIso ≪≫
      tildeFinsupp _
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let α : (Scheme.relativeDifferentials f).restrict V.ι ≅
      SheafOfModules.free (Module.Free.ChooseBasisIndex Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)]) :=
    (Scheme.Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec).symm.app _ ≪≫
      (Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app _ ≪≫
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso β ≪≫
      Scheme.Modules.restrictFreeIso _ _
  have hrk := Hartshorne.rank_fibre_of_restrict_iso_free _ α hxV
  have hfin : Cardinal.toNat
      (Cardinal.mk (Module.Free.ChooseBasisIndex Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)])) = n := by
    rw [← hrk]
    exact h x
  have hrank : Module.rank Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)] = n := by
    rw [← b.mk_eq_rank'', ← hfin, Cardinal.cast_toNat_of_lt_aleph0 Cardinal.mk_lt_aleph0]
  exact (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr hrank

/-- `f` is smooth of relative dimension `n` if and only if `f` is smooth and every fibre
`(Ω_{X/Y})_x ⊗ k(x)` has dimension `n`. -/
theorem Scheme.smoothOfRelativeDimension_iff_smooth_and_finrank_fibre {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    SmoothOfRelativeDimension n f ↔ Smooth f ∧
      ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          (Scheme.relativeDifferentials f).presheaf.stalk x) = n := by
  refine ⟨fun hf => ⟨SmoothOfRelativeDimension.smooth n f,
    Hartshorne.finrank_fibre_of_isLocallyFreeOfRank _ n
      (relativeDifferentials_isLocallyFreeOfRank_of_smoothOfRelativeDimension f n)⟩,
    fun ⟨_, h⟩ => smoothOfRelativeDimension_of_smooth_of_finrank_fibre f n h⟩

/-- A flat morphism locally of finite presentation with smooth scheme-theoretic fibres, whose
differential fibres `(Ω_{X/Y})_x ⊗ k(x)` all have dimension `n`, is smooth of relative
dimension `n`. -/
theorem Scheme.smoothOfRelativeDimension_of_flat_of_smooth_fiber {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [Flat f] (n : ℕ)
    (hfib : ∀ y : Y, Smooth (f.fiberToSpecResidueField y))
    (h : ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          (Scheme.relativeDifferentials f).presheaf.stalk x) = n) :
    SmoothOfRelativeDimension n f :=
  have : Smooth f := Smooth.of_smooth_fiberToSpecResidueField f hfib
  smoothOfRelativeDimension_of_smooth_of_finrank_fibre f n h

/-- Smoothness of relative dimension `n` passes to the scheme-theoretic fibre
`X_y → Spec k(y)`. -/
theorem Scheme.smoothOfRelativeDimension_fiberToSpecResidueField {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f] (y : Y) :
    SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹_›

end AlgebraicGeometry
