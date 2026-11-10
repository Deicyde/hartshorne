/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity
import Hartshorne.Scheme.Differentials.RelativeDifferentialsQuasicoherent
import Hartshorne.Scheme.Differentials.AffineSpaceDifferentials
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
`f^* M̃ ≅ (S ⊗_R M)~` is compatible with the adjunction units, the identification
`Ω_{X/Y}|_U ≅ (Ω_{B/A})~` sends derivatives to derivatives, and over a pushout of rings every
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

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The unit of the composite pullback, followed by `(g ∘ f)^* ≅ f^* g^*`, is the composite of
the units. -/
theorem unit_pullbackComp_inv (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules) :
    (pullbackPushforwardAdjunction (f ≫ g)).unit.app F ≫
      (pushforward (f ≫ g)).map ((pullbackComp f g).inv.app F) =
    (pullbackPushforwardAdjunction g).unit.app F ≫
      (pushforward g).map ((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj F)) ≫
      (pushforwardComp f g).hom.app _ := by
  have := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv F
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at this
  rw [← this, Category.assoc]
  rfl

/-- The unit of the pullback along `f`, followed by `f^* ≅ g^*` for `f = g`, is the unit along `g`
up to `f_* ≅ g_*`. -/
theorem unit_pullbackCongr_hom {f g : X ⟶ Y} (h : f = g) (F : Y.Modules) :
    (pullbackPushforwardAdjunction f).unit.app F ≫
      (pushforward f).map ((pullbackCongr h).hom.app F) =
    (pullbackPushforwardAdjunction g).unit.app F ≫ (pushforwardCongr h).inv.app _ := by
  subst h
  ext U : 1
  simp [pullbackCongr]
  rfl

/-- For an open immersion, the identification of restriction with pullback is compatible with the
adjunction units. -/
theorem unit_restrictFunctorIsoPullback_hom (f : X ⟶ Y) [IsOpenImmersion f] (F : Y.Modules) :
    (restrictAdjunction f).unit.app F ≫
      (pushforward f).map ((restrictFunctorIsoPullback f).hom.app F) =
    (pullbackPushforwardAdjunction f).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

end AlgebraicGeometry.Scheme.Modules

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

namespace AlgebraicGeometry.RelDiffLocal

variable {X Y U V : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ X) [IsOpenImmersion j] (g : U ⟶ V)
  (i : V ⟶ Y) [IsOpenImmersion i] (w : j ≫ f = g ≫ i)

/-- Under the locality isomorphism `Ω_{U/V} ≅ Ω_{X/Y}|_U`, the derivative of `j^♯ c` goes to the
derivative of `c`, on every open of `U`. -/
theorem restrictIso_hom_d (W : U.Opens) (c : Γ(X, j ''ᵁ W)) :
    (restrictIso f j g i w).hom.val.app (op W)
      ((Scheme.relativeDifferentialsDerivation g).d ((j.appIso W).hom c)) =
      (Scheme.relativeDifferentialsDerivation f).d (X := op (j ''ᵁ W)) c := by
  let r := restrictCorepresentable f j g i w
  have he : Scheme.relativeDifferentialsHomEquiv g _ (restrictIso f j g i w).hom =
      r.homEquiv (𝟙 _) := by
    change (Scheme.relativeDifferentialsHomEquiv g _)
      ((Scheme.relativeDifferentialsHomEquiv g _).symm (r.homEquiv (𝟙 _))) = _
    exact (Scheme.relativeDifferentialsHomEquiv g _).apply_symm_apply _
  rw [Scheme.relativeDifferentialsHomEquiv_apply] at he
  refine (PresheafOfModules.Derivation.congr_d he ((j.appIso W).hom c)).trans ?_
  change resD (Scheme.relativeDifferentialsHomEquiv f _
    ((Scheme.Modules.restrictAdjunction j).homEquiv _ _ (𝟙 _))) W ((j.appIso W).hom c) = _
  rw [Adjunction.homEquiv_id, Scheme.relativeDifferentialsHomEquiv_apply]
  unfold resD
  erw [PresheafOfModules.Derivation.postcomp_d_apply]
  have hc : (j.appIso W).inv ((j.appIso W).hom c) = c := Iso.hom_inv_id_apply _ _
  rw [hc]
  let D := Scheme.relativeDifferentialsDerivation f
  change (Scheme.relativeDifferentials f).presheaf.map _
    ((Scheme.relativeDifferentials f).presheaf.map _ (D.d (X := op (j ''ᵁ W)) c)) =
    D.d (X := op (j ''ᵁ W)) c
  refine (presheaf_map_map (Scheme.relativeDifferentials f) _ _ (𝟙 _) (𝟙 _) _).trans ?_
  rw [CategoryTheory.Functor.map_id]
  rfl

omit [IsOpenImmersion j] in
/-- The open immersion `Spec Γ(X, U) ⟶ X` of an affine open `U` sends the restriction of a section
`b` over `U` to the restriction of `b`, viewed as a global function on `Spec Γ(X, U)`. -/
theorem fromSpec_appIso_hom_res (U : X.affineOpens) (W : (Spec Γ(X, (U : X.Opens))).Opens)
    (hW : haveI := U.2.isOpenImmersion_fromSpec; U.2.fromSpec ''ᵁ W ≤ (U : X.Opens))
    (b : Γ(X, (U : X.Opens))) :
    haveI := U.2.isOpenImmersion_fromSpec
    (U.2.fromSpec.appIso W).hom (X.presheaf.map (homOfLE hW).op b) =
      (Spec Γ(X, (U : X.Opens))).presheaf.map W.leTop.op
        ((Scheme.ΓSpecIso Γ(X, (U : X.Opens))).inv b) := by
  rw [Scheme.Hom.appIso_hom, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply (X.presheaf.map _), Scheme.Hom.naturality,
    ConcreteCategory.comp_apply]
  erw [IsAffineOpen.fromSpec_app_self_apply (U.2 : IsAffineOpen (U : X.Opens)) b]
  exact AffineSpaceDifferentials.presheaf_map_map_map_apply _ _ _ _ _ _

omit [IsOpenImmersion j] in
/-- Under `Ω_{X/Y}|_U ≅ (Ω_{B/A})~` for affine opens `U ⊆ f⁻¹ V`, the derivative of (the
restriction of) `b ∈ B` is `d b`. -/
theorem affineIso_hom_d (U : X.affineOpens) (V : Y.affineOpens)
    (h : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens)) (W : (Spec Γ(X, (U : X.Opens))).Opens)
    (hW : haveI := U.2.isOpenImmersion_fromSpec; U.2.fromSpec ''ᵁ W ≤ (U : X.Opens))
    (b : Γ(X, (U : X.Opens))) :
    letI := (f.appLE V U h).hom.toAlgebra
    (affineIso f U V h).hom.val.app (op W)
      ((Scheme.relativeDifferentialsDerivation f).d (X.presheaf.map (homOfLE hW).op b)) =
      (tilde.toOpen (ModuleCat.of Γ(X, (U : X.Opens)) Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))])
        W).hom (KaehlerDifferential.D _ _ b) := by
  let := (f.appLE V U h).hom.toAlgebra
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  let e := restrictIso f U.2.fromSpec
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, (V : Y.Opens)) Γ(X, (U : X.Opens)))))
    V.2.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 h).symm
  have h1 := restrictIso_hom_d f U.2.fromSpec
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, (V : Y.Opens)) Γ(X, (U : X.Opens)))))
    V.2.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 h).symm W
    (X.presheaf.map (homOfLE hW).op b)
  have h2 : e.inv.val.app (op W)
      ((Scheme.relativeDifferentialsDerivation f).d (X.presheaf.map (homOfLE hW).op b)) =
      (Scheme.relativeDifferentialsDerivation
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, (V : Y.Opens)) Γ(X, (U : X.Opens)))))).d
        (X := op W) ((U.2.fromSpec.appIso W).hom (X.presheaf.map (homOfLE hW).op b)) := by
    have key : ∀ x, e.inv.val.app (op W) (e.hom.val.app (op W) x) = x := fun x =>
      congrArg (fun φ => φ.val.app (op W) x) e.hom_inv_id
    rw [← h1]
    exact key _
  change (Scheme.relativeDifferentialsSpecIso _ _).hom.val.app (op W)
    (e.inv.val.app (op W) _) = _
  rw [h2, fromSpec_appIso_hom_res U W hW b]
  exact Scheme.relativeDifferentialsSpecIso_hom_d _ _ W b

end AlgebraicGeometry.RelDiffLocal

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
