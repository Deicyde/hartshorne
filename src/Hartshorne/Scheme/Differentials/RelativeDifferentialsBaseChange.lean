/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.AffineTildeChangeOfRings
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base change for relative differentials

Hartshorne, *Algebraic Geometry*, II.8, Proposition 8.10 (p. 175).

Let `X' = X ×_Y Y'`, with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`. The canonical map
`g'^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` is the composite of the first map `g'^* Ω_{X/Y} ⟶ Ω_{X'/Y}` of the
transitivity sequence for `X' ⟶ X ⟶ Y`, the identification `Ω_{X'/Y}` along
`g' ≫ f = f' ≫ h`, and `Ω_{X'/Y} ⟶ Ω_{X'/Y'}`. It sends `1 ⊗ d b` to `d (g'^♯ b)`.

This file also collects the ingredients for checking that this map is an isomorphism on the affine
opens `U ×_W V` of a fibre product: such opens are affine and cover the fibre product, a morphism
of module sheaves is an isomorphism if it is one on every such open, the isomorphism
`f^* M̃ ≅ (S ⊗_R M)~` is compatible with the adjunction units, and over a pushout of rings every
linear map `B ⊗_A Ω_{A/R} → Ω_{B/S}` with `1 ⊗ d a ↦ d a` is bijective.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism of module sheaves is an isomorphism if every point lies in the image of an open
immersion along which its restriction is an isomorphism. -/
theorem Scheme.Modules.isIso_of_isIso_restrictFunctor_map {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N)
    (h : ∀ x : X, ∃ (U : Scheme.{u}) (j : U ⟶ X) (_ : IsOpenImmersion j),
      x ∈ j.opensRange ∧ IsIso ((Scheme.Modules.restrictFunctor j).map φ)) :
    IsIso φ := by
  refine Hartshorne.Ringed.modules_isIso_of_locally_bijective (R := X.sheaf) φ fun x => ?_
  obtain ⟨U, j, hj, hx, hiso⟩ := h x
  refine ⟨j.opensRange, hx, fun W hW => ?_⟩
  obtain ⟨W', rfl⟩ : ∃ W' : U.Opens, j ''ᵁ W' = W :=
    ⟨j ⁻¹ᵁ W, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hW]⟩
  have : IsIso (((Scheme.Modules.restrictFunctor j).map φ).val.app (op W')) :=
    ((SheafOfModules.forget U.ringCatSheaf ⋙ PresheafOfModules.evaluation _ (op W')).mapIso
      (@asIso _ _ _ _ ((Scheme.Modules.restrictFunctor j).map φ) hiso)).isIso_hom
  exact ConcreteCategory.bijective_of_isIso
    ((forget₂ _ AddCommGrpCat).map (((Scheme.Modules.restrictFunctor j).map φ).val.app (op W')))

/-- For affine opens `U ⊆ X`, `V ⊆ Y` lying over an affine open `W ⊆ Z`, the open
`U ×_W V` of `X ×_Z Y` is affine. -/
theorem IsAffineOpen.pullback_inf {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    {W : Z.Opens} (hW : IsAffineOpen W) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  let p : pullback (f.resLE W U hUW) (g.resLE W V hVW) ⟶ pullback f g :=
    pullback.map _ _ _ _ U.ι V.ι W.ι (by simp) (by simp)
  convert isAffineOpen_opensRange p
  ext1
  simp [p, Scheme.Pullback.range_map]

/-- A morphism of `𝒪_{X ×_Z Y}`-modules is an isomorphism if its restriction to every affine
open `U ×_W V`, for affine opens `U ⊆ X`, `V ⊆ Y`, `W ⊆ Z` with `U` and `V` over `W`, is. -/
theorem Scheme.Modules.isIso_of_isIso_pullback_inf {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    {M N : (Limits.pullback f g).Modules} (φ : M ⟶ N)
    (H : ∀ (U : X.affineOpens) (V : Y.affineOpens) (W : Z.affineOpens)
      (hUW : (U : X.Opens) ≤ f ⁻¹ᵁ W) (hVW : (V : Y.Opens) ≤ g ⁻¹ᵁ W),
      IsIso ((Hartshorne.QuasicoherentAbelianAux.specRestrictFunctor
        ⟨_, IsAffineOpen.pullback_inf U.2 V.2 W.2 hUW hVW⟩).map φ)) :
    IsIso φ := by
  refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map φ fun x => ?_
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := f (pullback.fst f g x)) trivial
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset
    (U := f ⁻¹ᵁ W) (x := pullback.fst f g x) hxW
  have hxW' : g (pullback.snd f g x) ∈ W := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hxW
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset
    (U := g ⁻¹ᵁ W) (x := pullback.snd f g x) hxW'
  have hP := IsAffineOpen.pullback_inf hU hV hW hUW hVW
  have := hP.isOpenImmersion_fromSpec
  exact ⟨_, hP.fromSpec, inferInstance, by rw [hP.opensRange_fromSpec]; exact ⟨hxU, hxV⟩,
    H ⟨U, hU⟩ ⟨V, hV⟩ ⟨W, hW⟩ hUW hVW⟩

end AlgebraicGeometry

namespace Hartshorne

open AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The isomorphism `f^* M̃ ≅ (S ⊗_R M)~` is compatible with the units: the global section of
`f^* M̃` pulled back from `m` goes to the global section `1 ⊗ m` of `(S ⊗_R M)~`. -/
theorem tildePullbackIso_hom_unit (M : ModuleCat.{u} R) :
    (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        ((tildePullbackIso φ).hom.app M) =
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).unit.app M ≫
      (pushforwardSpecΓIso φ).inv.app _ :=
  (unit_conjugateEquiv_symm _ _ _ M).symm

end Hartshorne

namespace KaehlerDifferential

open scoped TensorProduct

variable {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B] [IsScalarTower R A B]
  [IsScalarTower R S B]

/-- For `B = S ⊗_R A`, every `B`-linear map `B ⊗_A Ω_{A/R} → Ω_{B/S}` sending `1 ⊗ d a` to
`d a` is bijective: it is the base-change isomorphism. -/
theorem bijective_of_tmul_D [Algebra.IsPushout R S A B] (L : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄S])
    (hL : ∀ a : A, L (1 ⊗ₜ D R A a) = D S B (algebraMap A B a)) : Function.Bijective L := by
  let f : Ω[A⁄R] →ₗ[A] Ω[B⁄S] :=
    (L.restrictScalars A).comp (TensorProduct.mk A B Ω[A⁄R] 1)
  let f' : Ω[A⁄R] →ₗ[A] Ω[B⁄S] :=
    ((tensorKaehlerEquiv R S A B).toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A B Ω[A⁄R] 1)
  have hff' : f = f' := by
    ext a
    simp [f, f', hL]
  have hL' : L = (tensorKaehlerEquiv R S A B).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b ω
    have h1 : (b ⊗ₜ[A] ω : B ⊗[A] Ω[A⁄R]) = b • (1 ⊗ₜ ω) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, map_smul]
    exact congrArg (b • ·) (LinearMap.congr_fun hff' ω)
  rw [hL']
  exact (tensorKaehlerEquiv R S A B).bijective

end KaehlerDifferential

namespace AlgebraicGeometry.Scheme

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y' ⟶ Y)

/-- **The base-change map** `g'^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` for `X' = X ×_Y Y'`, with
`g' = pullback.fst f h` and `f' = pullback.snd f h`. -/
noncomputable def baseChangeRelativeDifferentialsMap :
    (Modules.pullback (pullback.fst f h)).obj (relativeDifferentials f) ⟶
      relativeDifferentials (pullback.snd f h) :=
  pullbackRelativeDifferentialsToComp (pullback.fst f h) f ≫
    (relativeDifferentialsCongr pullback.condition).hom ≫
    relativeDifferentialsCompToLeft (pullback.snd f h) h

/-- **Compatibility with the universal derivations**: the base-change map sends `1 ⊗ d_{X/Y} b`
to `d_{X'/Y'} (g'^♯ b)`. -/
theorem baseChangeRelativeDifferentialsMap_unit_d (V : X.Opens) (b : X.presheaf.obj (op V)) :
    (baseChangeRelativeDifferentialsMap f h).val.app (op (pullback.fst f h ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction (pullback.fst f h)).unit.app
        (relativeDifferentials f)).val.app (op V) ((relativeDifferentialsDerivation f).d b)) =
      (relativeDifferentialsDerivation (pullback.snd f h)).d
        ((pullback.fst f h).c.app (op V) b) := by
  change (relativeDifferentialsCompToLeft (pullback.snd f h) h).val.app _
    ((relativeDifferentialsCongr pullback.condition).hom.val.app _
      ((pullbackRelativeDifferentialsToComp (pullback.fst f h) f).val.app _ _)) = _
  rw [pullbackRelativeDifferentialsToComp_unit_d, relativeDifferentialsCongr_hom_d,
    relativeDifferentialsCompToLeft_d]

section HomExt

variable {X Y X' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ X)

/-- Morphisms out of `g^* Ω_{X/Y}` are determined by their values on the pulled-back
differentials `g^*(d_{X/Y} b)`. -/
theorem pullback_relativeDifferentials_hom_ext {N : X'.Modules}
    {φ ψ : (Modules.pullback g).obj (relativeDifferentials f) ⟶ N}
    (h : ∀ (V : X.Opens) (b : X.presheaf.obj (op V)),
      φ.val.app (op (g ⁻¹ᵁ V))
          (((Modules.pullbackPushforwardAdjunction g).unit.app (relativeDifferentials f)).val.app
            (op V) ((relativeDifferentialsDerivation f).d b)) =
        ψ.val.app (op (g ⁻¹ᵁ V))
          (((Modules.pullbackPushforwardAdjunction g).unit.app (relativeDifferentials f)).val.app
            (op V) ((relativeDifferentialsDerivation f).d b))) :
    φ = ψ := by
  apply ((Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply (relativeDifferentialsHomEquiv f _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext V b
  exact h V.unop b

end HomExt

end AlgebraicGeometry.Scheme
