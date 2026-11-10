/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.CotangentRelativeDifferentials
import Hartshorne.Cohomology.Semicontinuity.CoherentFiberDimension
import Hartshorne.Scheme.Differentials.RelativeDifferentialsAffineFibre
import Hartshorne.Cohomology.FlatFamilies.NormalFamilyFlat
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.Localization

/-!
# Smoothness by tangent-map surjectivity: scheme-level glue

Hartshorne, *Algebraic Geometry*, III, Proposition 10.4 (pp. 270–271).

## Main results

* `Hartshorne.SmoothTangent.finrank_tensor_kaehler_eq_of_isLocalization`: for `B = T_q` over
  a localization `A` of `R`, `κ(q) ⊗_T Ω_{T/R}` and `κ_B ⊗_B Ω_{B/A}` have the same dimension.
* `Hartshorne.SmoothTangent.finrank_fibre_relativeDifferentials_eq_stalk`: the fibre of `Ω_{X/Y}`
  at `x` has the dimension of `κ(x) ⊗ Ω_{𝒪_{X,x}/𝒪_{Y,f x}}`.
* `Hartshorne.SmoothTangent.moduleFiberDim_eq_of_forall_isClosed`: on a Jacobson scheme, a
  coherent sheaf whose fibres at closed points all have dimension `n` has all fibres of dimension
  `n`.
-/

namespace Hartshorne

noncomputable section

open IsLocalRing Module KaehlerDifferential CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace SmoothTangent

section Algebra

variable {R T A B : Type u} [CommRing R] [CommRing T] [CommRing A] [CommRing B] [IsLocalRing B]
  [Algebra R T] [Algebra T B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R T B]
  [IsScalarTower R A B]

omit [IsLocalRing B] [Algebra R T] [Algebra T B] [IsScalarTower R T B] in
/-- If `Ω_{A/R} = 0`, then `Ω_{B/R} → Ω_{B/A}` is injective. -/
theorem map_injective_of_subsingleton [Subsingleton Ω[A⁄R]] :
    Function.Injective (KaehlerDifferential.map R A B B) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  have ht : ∀ t : B ⊗[A] Ω[A⁄R], t = 0 := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul b η => rw [Subsingleton.elim η 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R A B ω).mp hω
  rw [ht t, map_zero]

/-- Let `B = T_q` be a localization of an `R`-algebra `T` at a prime `q`, and let `B` be an algebra
over an `R`-algebra `A` with `Ω_{A/R} = 0` (for instance a localization of `R`). Then
`dim κ(q) ⊗_T Ω_{T/R} = dim κ_B ⊗_B Ω_{B/A}`. -/
theorem finrank_tensor_kaehler_eq_of_isLocalization (q : Ideal T) [q.IsPrime]
    [IsLocalization.AtPrime B q] [Subsingleton Ω[A⁄R]] :
    finrank q.ResidueField (q.ResidueField ⊗[T] Ω[T⁄R]) =
      finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄A]) := by
  -- `Ω_{B/R} ≅ Ω_{B/A}`
  let e₁ : Ω[B⁄R] ≃ₗ[B] Ω[B⁄A] := LinearEquiv.ofBijective (KaehlerDifferential.map R A B B)
    ⟨map_injective_of_subsingleton, KaehlerDifferential.map_surjective R A B⟩
  -- `B ⊗_T Ω_{T/R} ≅ Ω_{B/R}`
  have : IsLocalization q.primeCompl B := ‹IsLocalization.AtPrime B q›
  have hbc : IsBaseChange B (KaehlerDifferential.map R R T B) :=
    (isLocalizedModule_iff_isBaseChange q.primeCompl B _).mp inferInstance
  let e₂ : ResidueField B ⊗[B] Ω[B⁄A] ≃ₗ[ResidueField B] ResidueField B ⊗[T] Ω[T⁄R] :=
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (ResidueField B) (ResidueField B)) (hbc.equiv.trans e₁).symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange T B (ResidueField B) (ResidueField B)
        Ω[T⁄R])
  -- the residue field of `T_q` maps to that of `B`
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) B
  let φ : Localization.AtPrime q →+* B := e.toRingEquiv.toRingHom
  have : IsLocalHom φ := ⟨fun a ha ↦ by
    have := ha.map (e.symm.toRingEquiv.toRingHom)
    simpa [φ] using this⟩
  let ψ : q.ResidueField →+* ResidueField B := ResidueField.map φ
  let : Algebra q.ResidueField (ResidueField B) := ψ.toAlgebra
  have : IsScalarTower T q.ResidueField (ResidueField B) := IsScalarTower.of_algebraMap_eq
    fun t ↦ by
      change residue B (algebraMap T B t) = ψ (residue _ (algebraMap T (Localization.AtPrime q) t))
      rw [ResidueField.map_residue]
      exact congrArg (residue B) (e.commutes t).symm
  let e₃ : ResidueField B ⊗[q.ResidueField] (q.ResidueField ⊗[T] Ω[T⁄R]) ≃ₗ[ResidueField B]
      ResidueField B ⊗[T] Ω[T⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange T q.ResidueField (ResidueField B)
      (ResidueField B) Ω[T⁄R]
  have hbase : finrank (ResidueField B)
      (ResidueField B ⊗[q.ResidueField] (q.ResidueField ⊗[T] Ω[T⁄R])) =
      finrank q.ResidueField (q.ResidueField ⊗[T] Ω[T⁄R]) := Module.finrank_baseChange
  rw [e₂.finrank_eq, ← e₃.finrank_eq, hbase]

end Algebra

section Scheme

/-- The fibre of `Ω_{X/Y}` at `x` has the dimension of `κ(x) ⊗ Ω_{𝒪_{X,x}/𝒪_{Y,f x}}`. -/
theorem finrank_fibre_relativeDifferentials_eq_stalk {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          (Scheme.relativeDifferentials f).presheaf.stalk x) =
      finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          Ω[X.presheaf.stalk x⁄Y.presheaf.stalk (f x)]) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (f ⁻¹ᵁ V : Set X) from hxV) (f ⁻¹ᵁ V).2
  obtain ⟨y, rfl⟩ : ∃ y, hU.fromSpec y = x := ⟨_, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  have : y.asIdeal.IsPrime := y.2
  let _ := (f.stalkMap (hU.fromSpec y)).hom.toAlgebra
  let : Algebra Γ(Y, V) (Y.presheaf.stalk (f (hU.fromSpec y))) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨f (hU.fromSpec y), hxV⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk (f (hU.fromSpec y)))
      (hV.primeIdealOf ⟨f (hU.fromSpec y), hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨f (hU.fromSpec y), hxV⟩
  have : Algebra.FormallyUnramified Γ(Y, V) (Y.presheaf.stalk (f (hU.fromSpec y))) :=
    Algebra.FormallyUnramified.of_isLocalization
      (hV.primeIdealOf ⟨f (hU.fromSpec y), hxV⟩).asIdeal.primeCompl
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hxU
  let : Algebra Γ(Y, V) (X.presheaf.stalk (hU.fromSpec y)) :=
    ((algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))).comp
      (algebraMap Γ(Y, V) Γ(X, U))).toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Y, V) (Y.presheaf.stalk (f (hU.fromSpec y)))
      (X.presheaf.stalk (hU.fromSpec y)) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
      homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      X.presheaf.germ_res_apply]
  refine (finrank_fibre_relativeDifferentials_affine f ⟨U, hU⟩ ⟨V, hV⟩ hUV y).trans ?_
  exact finrank_tensor_kaehler_eq_of_isLocalization (R := Γ(Y, V)) (T := Γ(X, U))
    (A := Y.presheaf.stalk (f (hU.fromSpec y))) y.asIdeal

/-- On a Jacobson scheme, a coherent sheaf whose fibres at all closed points have dimension `n` has
all fibres of dimension `n` (by upper semicontinuity of the fibre dimension). -/
theorem moduleFiberDim_eq_of_forall_isClosed {X : Scheme.{u}} [JacobsonSpace X] (G : X.Modules)
    (hG : IsCoherent G) {n : ℕ}
    (h : ∀ x : X, IsClosed ({x} : Set X) → moduleFiberDim G x = n) (x : X) :
    moduleFiberDim G x = n := by
  apply le_antisymm
  · by_contra hx
    rw [not_le] at hx
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
      (Z := {y : X | ((n + 1 : ℕ) : ℤ) ≤ (moduleFiberDim G y : ℤ)}) ⟨x, by simp; omega⟩
      (isClosed_setOf_le_moduleFiberDim_of_isCoherent G hG _).isLocallyClosed
    have := h z hzc
    simp [this] at hz
  · have hsub : closedPoints X ⊆ {y : X | (n : ℤ) ≤ (moduleFiberDim G y : ℤ)} := fun z hz ↦ by
      simp [h z hz]
    have := (isClosed_setOf_le_moduleFiberDim_of_isCoherent G hG n).closure_subset_iff.mpr hsub
    rw [closure_closedPoints] at this
    exact_mod_cast this (Set.mem_univ x)

/-- Flatness of stalk maps passes to generalizations: if `x ⤳ x₀` and `𝒪_{Y, f x₀} → 𝒪_{X, x₀}`
is flat, then so is `𝒪_{Y, f x} → 𝒪_{X, x}`. -/
theorem flat_stalkMap_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y) {x x₀ : X} (h : x ⤳ x₀)
    (h₀ : (f.stalkMap x₀).hom.Flat) : (f.stalkMap x).hom.Flat := by
  have hY : f x ⤳ f x₀ := f.base.hom.map_specializes h
  let _ : Algebra (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x₀) := (f.stalkMap x₀).hom.toAlgebra
  let _ : Algebra (X.presheaf.stalk x₀) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x₀)) (Y.presheaf.stalk (f x)) :=
    (Y.presheaf.stalkSpecializes hY).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x) :=
    ((algebraMap (X.presheaf.stalk x₀) (X.presheaf.stalk x)).comp
      (algebraMap (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x₀))).toAlgebra
  have : IsScalarTower (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x₀) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Y.presheaf.stalk (f x₀)) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (f.stalkSpecializes_stalkMap_apply x x₀ h a).symm
  have : Module.Flat (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x₀) := h₀
  have hB : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom) :=
    NormalFamily.isLocalization_stalkSpecializes h
  have : Module.Flat (X.presheaf.stalk x₀) (X.presheaf.stalk x) :=
    IsLocalization.flat _
      ((maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom).primeCompl
  have : Module.Flat (Y.presheaf.stalk (f x₀)) (X.presheaf.stalk x) :=
    Module.Flat.trans _ (X.presheaf.stalk x₀) _
  have hA : IsLocalization.AtPrime (Y.presheaf.stalk (f x))
      ((maximalIdeal (Y.presheaf.stalk (f x))).comap (Y.presheaf.stalkSpecializes hY).hom) :=
    NormalFamily.isLocalization_stalkSpecializes hY
  exact (Module.flat_iff_of_isLocalization (Y.presheaf.stalk (f x))
    ((maximalIdeal (Y.presheaf.stalk (f x))).comap (Y.presheaf.stalkSpecializes hY).hom).primeCompl
    (X.presheaf.stalk x)).mpr this

/-- On a Jacobson scheme, a morphism whose stalk maps at closed points are flat is flat. -/
theorem flat_of_forall_isClosed {X Y : Scheme.{u}} [JacobsonSpace X] (f : X ⟶ Y)
    (h : ∀ x : X, IsClosed ({x} : Set X) → (f.stalkMap x).hom.Flat) : Flat f := by
  refine Flat.of_stalkMap f fun x ↦ ?_
  obtain ⟨x₀, hx₀, hc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact flat_stalkMap_of_specializes f (specializes_iff_mem_closure.mpr hx₀) (h x₀ hc)

end Scheme

end SmoothTangent

end

end Hartshorne
