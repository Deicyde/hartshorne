/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity
import Hartshorne.Scheme.Differentials.RelativeDifferentialsQuasicoherent
import Hartshorne.Scheme.Differentials.AffineSpaceDifferentials
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.AffineTildeChangeOfRings
import Hartshorne.Scheme.PullbackQuasicoherent
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

The main results are `isIso_baseChangeRelativeDifferentialsMap`, that this map is an isomorphism,
and the resulting isomorphism `relativeDifferentialsBaseChangeIso : Ω_{X'/Y'} ≅ g'^* Ω_{X/Y}`.

Being an isomorphism is checked on the affine opens `W = U ×_V V'` of `X'`, for affine opens
`U ⊆ X`, `V ⊆ Y`, `V' ⊆ Y'` with `U` and `V'` over `V`; these cover `X'`. With `A = Γ(Y, V)`,
`B = Γ(X, U)`, `A' = Γ(Y', V')` and `B' = Γ(X', W)`, the ring `B'` is the pushout `A' ⊗_A B`, the
restriction of `g'^* Ω_{X/Y}` to `W` is `(B' ⊗_B Ω_{B/A})~`, and that of `Ω_{X'/Y'}` is
`(Ω_{B'/A'})~`. Under these identifications the map sends `1 ⊗ d b` to `d b`, so it is the
sheaf associated to the base-change isomorphism `B' ⊗_B Ω_{B/A} ≅ Ω_{B'/A'}` of Kähler
differentials.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

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
  exact TopCat.Presheaf.map_map_map_apply _ _ _ _ _ _

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

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- Morphisms of module sheaves commute with restriction of sections. -/
theorem app_presheaf_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U)
    (x : Γ(M, U)) : φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

/-- Two successive restrictions of sections of a module sheaf compose to a restriction. -/
theorem presheaf_map_map (M : X.Modules) {A B C : X.Opensᵒᵖ} (p : A ⟶ B) (q : B ⟶ C)
    (r : A ⟶ C) (x : M.presheaf.obj A) :
    M.presheaf.map q (M.presheaf.map p x) = M.presheaf.map r x :=
  (RelDiffLocal.presheaf_map_map M p q r (𝟙 C) x).trans
    ((ConcreteCategory.congr_hom (M.presheaf.map_id C) _).trans rfl)

/-- For an open immersion `f`, the identification of restriction with `f^*` sends the restriction
of `y` to the pulled-back section `f^* y`. -/
theorem restrictFunctorIsoPullback_hom_restrict_unit (f : X ⟶ Y) [IsOpenImmersion f]
    (G : Y.Modules) (T : Y.Opens) (y : Γ(G, T)) :
    ((restrictFunctorIsoPullback f).hom.app G).app (f ⁻¹ᵁ T)
      (G.presheaf.map (homOfLE (f.image_preimage_le T)).op y) =
      ((pullbackPushforwardAdjunction f).unit.app G).app T y :=
  ConcreteCategory.congr_hom
    (congrArg (fun φ => Hom.app φ T) (unit_restrictFunctorIsoPullback_hom f G)) y

/-- For an open immersion `f`, the identification of `f^*` with restriction sends `f^* y` to the
restriction of `y`. -/
theorem restrictFunctorIsoPullback_inv_unit (f : X ⟶ Y) [IsOpenImmersion f]
    (G : Y.Modules) (T : Y.Opens) (y : Γ(G, T)) :
    ((restrictFunctorIsoPullback f).inv.app G).app (f ⁻¹ᵁ T)
      (((pullbackPushforwardAdjunction f).unit.app G).app T y) =
      ((restrictAdjunction f).unit.app G).app T y := by
  rw [← restrictFunctorIsoPullback_hom_restrict_unit]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => Hom.app φ (f ⁻¹ᵁ T)) ((restrictFunctorIsoPullback f).hom_inv_id_app G)) _

/-- Pulling back a morphism `ζ` sends `f^* y` to `f^* (ζ y)`. -/
theorem pullback_map_unit (f : X ⟶ Y) {G H : Y.Modules} (ζ : G ⟶ H) (T : Y.Opens)
    (y : Γ(G, T)) :
    ((pullback f).map ζ).app (f ⁻¹ᵁ T) (((pullbackPushforwardAdjunction f).unit.app G).app T y) =
      ((pullbackPushforwardAdjunction f).unit.app H).app T (ζ.app T y) :=
  (ConcreteCategory.congr_hom
    (congrArg (fun φ => Hom.app φ T) ((pullbackPushforwardAdjunction f).unit.naturality ζ)) y).symm

/-- The isomorphism `(g ∘ f)^* ≅ f^* g^*` sends `(g ∘ f)^* s` to `f^* g^* s`. -/
theorem pullbackComp_inv_unit (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules) (T : Z.Opens)
    (s : Γ(F, T)) :
    ((pullbackComp f g).inv.app F).app ((f ≫ g) ⁻¹ᵁ T)
      (((pullbackPushforwardAdjunction (f ≫ g)).unit.app F).app T s) =
      ((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj F)).app (g ⁻¹ᵁ T)
        (((pullbackPushforwardAdjunction g).unit.app F).app T s) :=
  ConcreteCategory.congr_hom
    (congrArg (fun φ => Hom.app φ T) (unit_pullbackComp_inv f g F)) s

/-- The isomorphism `f^* g^* ≅ (g ∘ f)^*` sends `f^* g^* s` to `(g ∘ f)^* s`. -/
theorem pullbackComp_hom_unit (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules) (T : Z.Opens)
    (s : Γ(F, T)) :
    ((pullbackComp f g).hom.app F).app ((f ≫ g) ⁻¹ᵁ T)
      (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj F)).app (g ⁻¹ᵁ T)
        (((pullbackPushforwardAdjunction g).unit.app F).app T s)) =
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app F).app T s := by
  rw [← pullbackComp_inv_unit]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => Hom.app φ ((f ≫ g) ⁻¹ᵁ T)) ((pullbackComp f g).inv_hom_id_app F)) _

/-- For `f = g`, the isomorphism `g^* ≅ f^*` sends `g^* s` to `f^* s`, up to the equality of the
opens. -/
theorem pullbackCongr_inv_unit {f g : X ⟶ Y} (h : f = g) (F : Y.Modules) (T : Y.Opens)
    (s : Γ(F, T)) :
    ((pullbackCongr h).inv.app F).app (g ⁻¹ᵁ T)
      (((pullbackPushforwardAdjunction g).unit.app F).app T s) =
      ((pullback f).obj F).presheaf.map (eqToHom (by rw [h])).op
        (((pullbackPushforwardAdjunction f).unit.app F).app T s) := by
  subst h
  simp [pullbackCongr]

end AlgebraicGeometry.Scheme.Modules

namespace Hartshorne

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

open scoped TensorProduct in
/-- On global sections, `f^* M̃ ≅ (S ⊗_R M)~` sends the pulled-back section of `m` to `1 ⊗ m`. -/
theorem tildePullbackIso_hom_unit_apply (M : ModuleCat.{u} R) (m : M) :
    ((tildePullbackIso φ).hom.app M).val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).val.app
        (op ⊤) ((tilde.toOpen M ⊤).hom m)) =
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom
        ((1 : S) ⊗ₜ[R] m : (ModuleCat.extendScalars φ.hom).obj M) := by
  have h := ConcreteCategory.congr_hom (tildePullbackIso_hom_unit φ M) m
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  exact h

end Hartshorne

namespace Hartshorne.PullbackQuasicoherent

open Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 1000000 in
/-- On global sections, the inverse of `(f^*F)|_V ≅ (Γ(V) ⊗ M)~` sends the restriction of a
pulled-back section `f^* s` to the image of `s` under `F|_U ≅ M̃` and
`M̃ ⟶ f^* M̃ ≅ (Γ(V) ⊗ M)~`. -/
theorem specRestrictionPullbackIso_inv_unit (F : Y.Modules) (U : Y.affineOpens)
    (V : X.affineOpens) (h : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))
    (M : ModuleCat.{u} Γ(Y, (U : Y.Opens)))
    (e : (tilde.functor Γ(Y, (U : Y.Opens))).obj M ≅ specRestriction F U)
    (T : Y.Opens) (s : Γ(F, T))
    (hT : haveI := V.2.isOpenImmersion_fromSpec; V.2.fromSpec ''ᵁ ⊤ ≤ f ⁻¹ᵁ T)
    (hT' : ⊤ ≤ Spec.map (f.appLE U V h) ⁻¹ᵁ (U.2.fromSpec ⁻¹ᵁ T)) :
    haveI := U.2.isOpenImmersion_fromSpec
    haveI := V.2.isOpenImmersion_fromSpec
    (specRestrictionPullbackIso f F U V h M e).inv.app ⊤
      (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hT).op
        (((pullbackPushforwardAdjunction f).unit.app F).app T s)) =
    ((tildePullbackIso (f.appLE U V h)).hom.app M).app ⊤
      (((Scheme.Modules.pullback (Spec.map (f.appLE U V h))).obj
          ((tilde.functor Γ(Y, (U : Y.Opens))).obj M)).presheaf.map (homOfLE hT').op
        (((pullbackPushforwardAdjunction (Spec.map (f.appLE U V h))).unit.app
            ((tilde.functor Γ(Y, (U : Y.Opens))).obj M)).app (U.2.fromSpec ⁻¹ᵁ T)
          (e.inv.app (U.2.fromSpec ⁻¹ᵁ T)
            (((restrictAdjunction U.2.fromSpec).unit.app F).app T s)))) := by
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have pa : Spec.map (f.appLE U V h) ≫ U.2.fromSpec = V.2.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 h
  have h1 : ⊤ ≤ V.2.fromSpec ⁻¹ᵁ (f ⁻¹ᵁ T) := fun x _ => hT ⟨x, trivial, rfl⟩
  have e1 : ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hT).op
      (((pullbackPushforwardAdjunction f).unit.app F).app T s) =
      (((Scheme.Modules.pullback f).obj F).restrict V.2.fromSpec).presheaf.map (homOfLE h1).op
        (((Scheme.Modules.pullback f).obj F).presheaf.map
          (homOfLE (V.2.fromSpec.image_preimage_le (f ⁻¹ᵁ T))).op
          (((pullbackPushforwardAdjunction f).unit.app F).app T s)) :=
    (presheaf_map_map _ _ _ _ _).symm
  have s1 : ((restrictFunctorIsoPullback V.2.fromSpec).hom.app ((Scheme.Modules.pullback f).obj
      F)).app ⊤
      (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hT).op
          (((pullbackPushforwardAdjunction f).unit.app F).app T s)) =
      ((Scheme.Modules.pullback V.2.fromSpec).obj ((Scheme.Modules.pullback f).obj
          F)).presheaf.map (homOfLE h1).op
        (((pullbackPushforwardAdjunction V.2.fromSpec).unit.app ((Scheme.Modules.pullback f).obj
            F)).app (f ⁻¹ᵁ T)
          (((pullbackPushforwardAdjunction f).unit.app F).app T s)) := by
    rw [e1]
    exact (app_presheaf_map _ _ _).trans
      (congrArg _ (restrictFunctorIsoPullback_hom_restrict_unit _ _ _ _))
  have s2 : ((pullbackComp V.2.fromSpec f).hom.app F).app ⊤
      (((Scheme.Modules.pullback V.2.fromSpec).obj ((Scheme.Modules.pullback f).obj
          F)).presheaf.map (homOfLE h1).op
        (((pullbackPushforwardAdjunction V.2.fromSpec).unit.app ((Scheme.Modules.pullback f).obj
            F)).app (f ⁻¹ᵁ T)
          (((pullbackPushforwardAdjunction f).unit.app F).app T s))) =
      ((Scheme.Modules.pullback (V.2.fromSpec ≫ f)).obj F).presheaf.map (homOfLE h1).op
        (((pullbackPushforwardAdjunction (V.2.fromSpec ≫ f)).unit.app F).app T s) :=
    (app_presheaf_map _ _ _).trans (congrArg _ (pullbackComp_hom_unit V.2.fromSpec f F T s))
  have h3 : ⊤ ≤ ((Spec.map (f.appLE U V h)) ≫ U.2.fromSpec) ⁻¹ᵁ T := hT'
  have s3 : ((pullbackCongr pa).inv.app F).app ⊤
      (((Scheme.Modules.pullback (V.2.fromSpec ≫ f)).obj F).presheaf.map (homOfLE h1).op
        (((pullbackPushforwardAdjunction (V.2.fromSpec ≫ f)).unit.app F).app T s)) =
      ((Scheme.Modules.pullback ((Spec.map (f.appLE U V h)) ≫ U.2.fromSpec)).obj
          F).presheaf.map (homOfLE h3).op
        (((pullbackPushforwardAdjunction ((Spec.map (f.appLE U V h)) ≫ U.2.fromSpec)).unit.app
            F).app T s) :=
    (app_presheaf_map _ _ _).trans ((congrArg _ (pullbackCongr_inv_unit pa F T s)).trans
      (presheaf_map_map _ _ _ _ _))
  have s4 : ((pullbackComp (Spec.map (f.appLE U V h)) U.2.fromSpec).inv.app F).app ⊤
      (((Scheme.Modules.pullback ((Spec.map (f.appLE U V h)) ≫ U.2.fromSpec)).obj F).presheaf.map
          (homOfLE h3).op
        (((pullbackPushforwardAdjunction ((Spec.map (f.appLE U V h)) ≫ U.2.fromSpec)).unit.app
            F).app T s)) =
      ((Scheme.Modules.pullback (Spec.map (f.appLE U V h))).obj ((Scheme.Modules.pullback
          U.2.fromSpec).obj F)).presheaf.map
        (homOfLE hT').op
        (((pullbackPushforwardAdjunction (Spec.map (f.appLE U V h))).unit.app
            ((Scheme.Modules.pullback U.2.fromSpec).obj F)).app
          (U.2.fromSpec ⁻¹ᵁ T)
          (((pullbackPushforwardAdjunction U.2.fromSpec).unit.app F).app T s)) :=
    (app_presheaf_map _ _ _).trans (congrArg _ (pullbackComp_inv_unit (Spec.map (f.appLE U V h))
        U.2.fromSpec F T s))
  have s5 : ((Scheme.Modules.pullback (Spec.map (f.appLE U V h))).map
        ((restrictFunctorIsoPullback U.2.fromSpec).inv.app F ≫ e.inv)).app ⊤
      (((Scheme.Modules.pullback (Spec.map (f.appLE U V h))).obj ((Scheme.Modules.pullback
          U.2.fromSpec).obj F)).presheaf.map
        (homOfLE hT').op
        (((pullbackPushforwardAdjunction (Spec.map (f.appLE U V h))).unit.app
            ((Scheme.Modules.pullback U.2.fromSpec).obj F)).app
          (U.2.fromSpec ⁻¹ᵁ T)
          (((pullbackPushforwardAdjunction U.2.fromSpec).unit.app F).app T s))) =
      ((Scheme.Modules.pullback (Spec.map (f.appLE U V h))).obj
          ((tilde.functor Γ(Y, (U : Y.Opens))).obj M)).presheaf.map
        (homOfLE hT').op
        (((pullbackPushforwardAdjunction (Spec.map (f.appLE U V h))).unit.app
            ((tilde.functor Γ(Y, (U : Y.Opens))).obj M)).app (U.2.fromSpec ⁻¹ᵁ T)
          (e.inv.app (U.2.fromSpec ⁻¹ᵁ T)
            (((restrictAdjunction U.2.fromSpec).unit.app F).app T s))) := by
    refine (app_presheaf_map _ _ _).trans (congrArg _ ((pullback_map_unit _ _ _ _).trans ?_))
    rw [Hom.comp_app]
    exact congrArg _ (congrArg (e.inv.app (U.2.fromSpec ⁻¹ᵁ T))
        (restrictFunctorIsoPullback_inv_unit U.2.fromSpec F T s))
  refine Eq.trans (b := ((tildePullbackIso (f.appLE U V h)).hom.app M).app ⊤
    (((Scheme.Modules.pullback (Spec.map (f.appLE U V h))).map
        ((restrictFunctorIsoPullback U.2.fromSpec).inv.app F ≫ e.inv)).app ⊤
      (((pullbackComp (Spec.map (f.appLE U V h)) U.2.fromSpec).inv.app F).app ⊤
        (((pullbackCongr pa).inv.app F).app ⊤
          (((pullbackComp V.2.fromSpec f).hom.app F).app ⊤
            (((restrictFunctorIsoPullback V.2.fromSpec).hom.app
                ((Scheme.Modules.pullback f).obj F)).app ⊤
              (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hT).op
                (((pullbackPushforwardAdjunction f).unit.app F).app T s)))))))) rfl ?_
  rw [s1, s2, s3, s4, s5]

end Hartshorne.PullbackQuasicoherent

namespace AlgebraicGeometry.Scheme

open Hartshorne Hartshorne.PullbackQuasicoherent Hartshorne.QuasicoherentAbelianAux Modules
open scoped TensorProduct

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y' ⟶ Y) (U : X.affineOpens) (V : Y.affineOpens)
  (V' : Y'.affineOpens) (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens))
  (hV'V : (V' : Y'.Opens) ≤ h ⁻¹ᵁ (V : Y.Opens))

/-- The affine open `U ×_V V'` of `X ×_Y Y'`. -/
noncomputable abbrev baseChangeAffineOpen : (pullback f h).affineOpens :=
  ⟨_, IsAffineOpen.pullback_inf U.2 V'.2 V.2 hUV hV'V⟩

/-- On `W = U ×_V V'`, the inverse of `(g'^*Ω_{X/Y})|_W ≅ (Γ(W) ⊗_B Ω_{B/A})~` sends the
restriction of `g'^*(d b)` to `1 ⊗ d b`. -/
theorem baseChange_specRestrictionPullbackIso_inv (b : Γ(X, (U : X.Opens)))
    (hT : haveI := (baseChangeAffineOpen f h U V V' hUV hV'V).2.isOpenImmersion_fromSpec
      (baseChangeAffineOpen f h U V V' hUV hV'V).2.fromSpec ''ᵁ ⊤ ≤
        pullback.fst f h ⁻¹ᵁ (U : X.Opens)) :
    letI := (f.appLE V U hUV).hom.toAlgebra
    (specRestrictionPullbackIso (pullback.fst f h) (relativeDifferentials f) U
        (baseChangeAffineOpen f h U V V' hUV hV'V) inf_le_left _
        (RelDiffLocal.affineIso f U V hUV).symm).inv.app ⊤
      (((Modules.pullback (pullback.fst f h)).obj (relativeDifferentials f)).presheaf.map
        (homOfLE hT).op
        (((pullbackPushforwardAdjunction (pullback.fst f h)).unit.app
          (relativeDifferentials f)).app U ((relativeDifferentialsDerivation f).d b))) =
      (tilde.toOpen ((ModuleCat.extendScalars ((pullback.fst f h).appLE U
        (baseChangeAffineOpen f h U V V' hUV hV'V) inf_le_left).hom).obj
          (ModuleCat.of Γ(X, (U : X.Opens)) Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))])) ⊤).hom
        ((1 : Γ(pullback f h, (baseChangeAffineOpen f h U V V' hUV hV'V : (pullback f h).Opens)))
          ⊗ₜ[Γ(X, (U : X.Opens))] (KaehlerDifferential.D _ _ b :
            Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))])) := by
  let := (f.appLE V U hUV).hom.toAlgebra
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hT' : ⊤ ≤ Spec.map ((pullback.fst f h).appLE U (baseChangeAffineOpen f h U V V' hUV hV'V)
      inf_le_left) ⁻¹ᵁ (U.2.fromSpec ⁻¹ᵁ (U : X.Opens)) := by
    intro x _
    show (Spec.map _).base x ∈ U.2.fromSpec ⁻¹ᵁ (U : X.Opens)
    rw [U.2.fromSpec_preimage_self]
    trivial
  refine (specRestrictionPullbackIso_inv_unit _ _ _ _ _ _ _ _ _ hT hT').trans ?_
  have r12 : ((RelDiffLocal.affineIso f U V hUV).symm.inv).app (U.2.fromSpec ⁻¹ᵁ (U : X.Opens))
      (((restrictAdjunction U.2.fromSpec).unit.app (relativeDifferentials f)).app U
        ((relativeDifferentialsDerivation f).d b)) =
      (tilde.toOpen (ModuleCat.of Γ(X, (U : X.Opens)) Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))])
        (U.2.fromSpec ⁻¹ᵁ (U : X.Opens))).hom (KaehlerDifferential.D _ _ b) := by
    refine Eq.trans ?_ (RelDiffLocal.affineIso_hom_d f U V hUV (U.2.fromSpec ⁻¹ᵁ (U : X.Opens))
      (U.2.fromSpec.image_preimage_le _) b)
    exact congrArg _ ((relativeDifferentialsDerivation f).d_map _ b).symm
  rw [r12]
  refine Eq.trans ?_ (Hartshorne.tildePullbackIso_hom_unit_apply _ _ _)
  refine congrArg _ ?_
  have r3 : (tilde.toOpen
      (ModuleCat.of Γ(X, (U : X.Opens)) Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))])
      (U.2.fromSpec ⁻¹ᵁ (U : X.Opens))).hom (KaehlerDifferential.D _ _ b) =
      ((tilde.functor _).obj (ModuleCat.of Γ(X, (U : X.Opens))
        Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))])).presheaf.map (homOfLE le_top).op
        ((tilde.toOpen (ModuleCat.of Γ(X, (U : X.Opens))
          Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))]) ⊤).hom (KaehlerDifferential.D _ _ b)) := rfl
  rw [r3]
  refine (congrArg _ (app_presheaf_map _ _ _)).trans ((presheaf_map_map _ _ _ (𝟙 _) _).trans ?_)
  exact (ConcreteCategory.congr_hom (CategoryTheory.Functor.map_id _ _) _).trans rfl

end AlgebraicGeometry.Scheme

namespace Hartshorne

open AlgebraicGeometry

/-- A morphism `M̃ ⟶ Ñ` that is given on global sections by a bijective linear map is an
isomorphism. -/
theorem tilde_isIso_of_toOpen {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (Ψ : (tilde.functor R).obj M ⟶ (tilde.functor R).obj N) (L : M ⟶ N)
    (hL : Function.Bijective L)
    (hΨ : ∀ m : M, Ψ.val.app (op ⊤) ((tilde.toOpen M ⊤).hom m) = (tilde.toOpen N ⊤).hom (L m)) :
    IsIso Ψ := by
  have e : Ψ = (tilde.functor R).map L := by
    apply (tilde.adjunction.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext m
    exact (hΨ m).trans (Scheme.tilde_map_app_toOpen L ⊤ m).symm
  have : IsIso L := (ConcreteCategory.isIso_iff_bijective L).mpr hL
  rw [e]
  infer_instance

end Hartshorne

namespace AlgebraicGeometry.Scheme

open Hartshorne Hartshorne.PullbackQuasicoherent Hartshorne.QuasicoherentAbelianAux Modules
open scoped TensorProduct

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y' ⟶ Y) (U : X.affineOpens) (V : Y.affineOpens)
  (V' : Y'.affineOpens) (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens))
  (hV'V : (V' : Y'.Opens) ≤ h ⁻¹ᵁ (V : Y.Opens))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- On `W = U ×_V V'`, the base-change map, read through `(g'^*Ω_{X/Y})|_W ≅ (Γ(W) ⊗_B Ω_{B/A})~`
and `Ω_{X'/Y'}|_W ≅ (Ω_{Γ(W)/A'})~`, sends `1 ⊗ d b` to `d b`. -/
theorem baseChange_local_toOpen (b : Γ(X, (U : X.Opens))) :
    let := (f.appLE V U hUV).hom.toAlgebra
    let := ((pullback.snd f h).appLE V' (baseChangeAffineOpen f h U V V' hUV hV'V)
      inf_le_right).hom.toAlgebra
    ((specRestrictionPullbackIso (pullback.fst f h) (relativeDifferentials f) U
        (baseChangeAffineOpen f h U V V' hUV hV'V) inf_le_left _
        (RelDiffLocal.affineIso f U V hUV).symm).hom ≫
      (specRestrictFunctor (baseChangeAffineOpen f h U V V' hUV hV'V)).map
        (baseChangeRelativeDifferentialsMap f h) ≫
      (RelDiffLocal.affineIso (pullback.snd f h) (baseChangeAffineOpen f h U V V' hUV hV'V) V'
        inf_le_right).hom).val.app (op ⊤)
      ((tilde.toOpen ((ModuleCat.extendScalars ((pullback.fst f h).appLE U
        (baseChangeAffineOpen f h U V V' hUV hV'V) inf_le_left).hom).obj
          (ModuleCat.of Γ(X, (U : X.Opens)) Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))])) ⊤).hom
        ((1 : Γ(pullback f h, (baseChangeAffineOpen f h U V V' hUV hV'V : (pullback f h).Opens)))
          ⊗ₜ[Γ(X, (U : X.Opens))] (KaehlerDifferential.D _ _ b :
            Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))]))) =
      (tilde.toOpen (ModuleCat.of Γ(pullback f h,
          (baseChangeAffineOpen f h U V V' hUV hV'V : (pullback f h).Opens))
        Ω[Γ(pullback f h, (baseChangeAffineOpen f h U V V' hUV hV'V : (pullback f h).Opens))⁄
          Γ(Y', (V' : Y'.Opens))]) ⊤).hom
        (KaehlerDifferential.D _ _ ((pullback.fst f h).appLE U
          (baseChangeAffineOpen f h U V V' hUV hV'V) inf_le_left b)) := by
  intro _ _
  have : IsOpenImmersion (baseChangeAffineOpen f h U V V' hUV hV'V).2.fromSpec :=
    (baseChangeAffineOpen f h U V V' hUV hV'V).2.isOpenImmersion_fromSpec
  have hW : (baseChangeAffineOpen f h U V V' hUV hV'V).2.fromSpec ''ᵁ ⊤ ≤
      (baseChangeAffineOpen f h U V V' hUV hV'V : (pullback f h).Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      (baseChangeAffineOpen f h U V V' hUV hV'V).2.opensRange_fromSpec]
  have hT : (baseChangeAffineOpen f h U V V' hUV hV'V).2.fromSpec ''ᵁ ⊤ ≤
      pullback.fst f h ⁻¹ᵁ (U : X.Opens) := hW.trans inf_le_left
  have e0 := baseChange_specRestrictionPullbackIso_inv f h U V V' hUV hV'V b hT
  set SR := specRestrictionPullbackIso (pullback.fst f h) (relativeDifferentials f) U
    (baseChangeAffineOpen f h U V V' hUV hV'V) inf_le_left _
    (RelDiffLocal.affineIso f U V hUV).symm
  set AF := RelDiffLocal.affineIso (pullback.snd f h) (baseChangeAffineOpen f h U V V' hUV hV'V)
    V' inf_le_right
  set W := baseChangeAffineOpen f h U V V' hUV hV'V
  have e1 : ∀ y, SR.hom.app ⊤ (SR.inv.app ⊤ y) = y := fun y => by
    have := ConcreteCategory.congr_hom (congrArg (fun φ => Modules.Hom.app φ ⊤) SR.inv_hom_id) y
    exact this
  have e2 : ((specRestrictFunctor W).map (baseChangeRelativeDifferentialsMap f h)).app ⊤
      (((Modules.pullback (pullback.fst f h)).obj (relativeDifferentials f)).presheaf.map
        (homOfLE hT).op (((pullbackPushforwardAdjunction (pullback.fst f h)).unit.app
          (relativeDifferentials f)).app U ((relativeDifferentialsDerivation f).d b))) =
      (relativeDifferentialsDerivation (pullback.snd f h)).d
        ((pullback f h).presheaf.map (homOfLE hT).op ((pullback.fst f h).app U b)) := by
    refine (app_presheaf_map (baseChangeRelativeDifferentialsMap f h) (homOfLE hT) _).trans ?_
    refine (congrArg _ (baseChangeRelativeDifferentialsMap_unit_d f h U b)).trans ?_
    exact ((relativeDifferentialsDerivation (pullback.snd f h)).d_map _ _).symm
  have e3 : (pullback f h).presheaf.map (homOfLE hT).op ((pullback.fst f h).app U b) =
      (pullback f h).presheaf.map (homOfLE hW).op
        ((pullback.fst f h).appLE U W inf_le_left b) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    exact (TopCat.Presheaf.map_map_apply _ _ _ _ _).symm
  have e4 := RelDiffLocal.affineIso_hom_d (pullback.snd f h) W V' inf_le_right ⊤ hW
    ((pullback.fst f h).appLE U W inf_le_left b)
  refine (congrArg (fun z => AF.hom.app ⊤ (((specRestrictFunctor W).map
    (baseChangeRelativeDifferentialsMap f h)).app ⊤ (SR.hom.app ⊤ z))) e0.symm).trans ?_
  refine (congrArg (fun z => AF.hom.app ⊤ (((specRestrictFunctor W).map
    (baseChangeRelativeDifferentialsMap f h)).app ⊤ z)) (e1 _)).trans ?_
  rw [e2, e3]
  exact e4

/-- The ring of the affine open `U ×_V V'` is the pushout of `Γ(X, U) ← Γ(Y, V) → Γ(Y', V')`. -/
theorem baseChange_isPushout :
    IsPushout (f.appLE V U hUV) (h.appLE V V' hV'V)
      ((pullback.fst f h).appLE U (baseChangeAffineOpen f h U V V' hUV hV'V) inf_le_left)
      ((pullback.snd f h).appLE V' (baseChangeAffineOpen f h U V V' hUV hV'V) inf_le_right) := by
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f h) (US := (V : Y.Opens))
    (UT := (V' : Y'.Opens)) (UX := (U : X.Opens)) hV'V hUV
    (UY := (baseChangeAffineOpen f h U V V' hUV hV'V : (pullback f h).Opens)) rfl
  have : IsAffine (U : X.Opens).toScheme := U.2
  have : IsAffine (V : Y.Opens).toScheme := V.2
  have : IsAffine (V' : Y'.Opens).toScheme := V'.2
  exact (isPushout_appTop_of_isPullback H).of_iso (Scheme.Opens.topIso _) (Scheme.Opens.topIso _)
    (Scheme.Opens.topIso _) (Scheme.Opens.topIso _)
    (arrowResLEAppIso f _ _ hUV).hom.w.symm (arrowResLEAppIso h _ _ hV'V).hom.w.symm
    (arrowResLEAppIso (pullback.fst f h) _ _ _).hom.w.symm
    (arrowResLEAppIso (pullback.snd f h) _ _ _).hom.w.symm

set_option maxRecDepth 10000 in
/-- The base-change map is an isomorphism on every affine open `U ×_V V'`. -/
theorem baseChange_isIso_specRestrict :
    IsIso ((specRestrictFunctor (baseChangeAffineOpen f h U V V' hUV hV'V)).map
      (baseChangeRelativeDifferentialsMap f h)) := by
  set W := baseChangeAffineOpen f h U V V' hUV hV'V with hWdef
  let _ : Algebra Γ(Y, (V : Y.Opens)) Γ(X, (U : X.Opens)) := (f.appLE V U hUV).hom.toAlgebra
  let _ : Algebra Γ(Y, (V : Y.Opens)) Γ(Y', (V' : Y'.Opens)) := (h.appLE V V' hV'V).hom.toAlgebra
  let _ : Algebra Γ(X, (U : X.Opens)) Γ(pullback f h, (W : (pullback f h).Opens)) :=
    ((pullback.fst f h).appLE U W inf_le_left).hom.toAlgebra
  let _ : Algebra Γ(Y', (V' : Y'.Opens)) Γ(pullback f h, (W : (pullback f h).Opens)) :=
    ((pullback.snd f h).appLE V' W inf_le_right).hom.toAlgebra
  let _ : Algebra Γ(Y, (V : Y.Opens)) Γ(pullback f h, (W : (pullback f h).Opens)) :=
    (f.appLE V U hUV ≫ (pullback.fst f h).appLE U W inf_le_left).hom.toAlgebra
  have hP := baseChange_isPushout f h U V V' hUV hV'V
  have : IsScalarTower Γ(Y, (V : Y.Opens)) Γ(X, (U : X.Opens))
      Γ(pullback f h, (W : (pullback f h).Opens)) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, (V : Y.Opens)) Γ(Y', (V' : Y'.Opens))
      Γ(pullback f h, (W : (pullback f h).Opens)) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hP.w)
  have : Algebra.IsPushout Γ(Y, (V : Y.Opens)) Γ(Y', (V' : Y'.Opens)) Γ(X, (U : X.Opens))
      Γ(pullback f h, (W : (pullback f h).Opens)) :=
    CommRingCat.isPushout_iff_isPushout.mp hP.flip
  set SR := specRestrictionPullbackIso (pullback.fst f h) (relativeDifferentials f) U
    W inf_le_left _ (RelDiffLocal.affineIso f U V hUV).symm with hSR
  set AF := RelDiffLocal.affineIso (pullback.snd f h) W V' inf_le_right with hAF
  let L0 : (ModuleCat.extendScalars ((pullback.fst f h).appLE U W inf_le_left).hom).obj
      (ModuleCat.of Γ(X, (U : X.Opens)) Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))]) ⟶
      ModuleCat.of Γ(pullback f h, (W : (pullback f h).Opens))
        Ω[Γ(pullback f h, (W : (pullback f h).Opens))⁄Γ(Y', (V' : Y'.Opens))] :=
    ModuleCat.ofHom (X := (ModuleCat.extendScalars ((pullback.fst f h).appLE U W
        inf_le_left).hom).obj
      (ModuleCat.of Γ(X, (U : X.Opens)) Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))]))
      (Y := ModuleCat.of Γ(pullback f h, (W : (pullback f h).Opens))
        Ω[Γ(pullback f h, (W : (pullback f h).Opens))⁄Γ(Y', (V' : Y'.Opens))])
      (KaehlerDifferential.tensorKaehlerEquiv Γ(Y, (V : Y.Opens))
      Γ(Y', (V' : Y'.Opens)) Γ(X, (U : X.Opens)) Γ(pullback f h, (W : (pullback f
          h).Opens))).toLinearMap
  have hL0 : Function.Bijective L0 := (KaehlerDifferential.tensorKaehlerEquiv _ _ _ _).bijective
  have hΨ : IsIso (SR.hom ≫ (specRestrictFunctor W).map (baseChangeRelativeDifferentialsMap f h) ≫
      AF.hom) := by
    refine tilde_isIso_of_toOpen _ L0 hL0 fun m => ?_
    have key : tilde.toOpen _ ⊤ ≫ (modulesSpecToSheaf.map (SR.hom ≫ (specRestrictFunctor W).map
        (baseChangeRelativeDifferentialsMap f h) ≫ AF.hom)).1.app (op ⊤) =
        L0 ≫ tilde.toOpen _ ⊤ := by
      apply ((ModuleCat.extendRestrictScalarsAdj
        ((pullback.fst f h).appLE U W inf_le_left).hom).homEquiv _ _).injective
      apply ModuleCat.hom_ext
      refine LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation _ _) fun b => ?_
      refine (baseChange_local_toOpen f h U V V' hUV hV'V b).trans ?_
      refine congrArg (tilde.toOpen _ ⊤).hom ?_
      exact ((KaehlerDifferential.tensorKaehlerEquiv_tmul_D _ _ _ _ _ _).trans
        (one_smul _ _)).symm
    exact ConcreteCategory.congr_hom key m
  have := IsIso.of_isIso_comp_left SR.hom
    ((specRestrictFunctor W).map (baseChangeRelativeDifferentialsMap f h) ≫ AF.hom)
  exact IsIso.of_isIso_comp_right ((specRestrictFunctor W).map
    (baseChangeRelativeDifferentialsMap f h)) AF.hom

/-- **Base change for relative differentials** (Hartshorne II.8.10): for `X' = X ×_Y Y'`, the
base-change map `g'^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` is an isomorphism. -/
theorem isIso_baseChangeRelativeDifferentialsMap :
    IsIso (baseChangeRelativeDifferentialsMap f h) :=
  Modules.isIso_of_isIso_pullback_inf _ fun U V' V hUV hV'V =>
    baseChange_isIso_specRestrict f h U V V' hUV hV'V

/-- **Base change for relative differentials** (Hartshorne II.8.10): for `X' = X ×_Y Y'` with
projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`, `Ω_{X'/Y'} ≅ g'^* Ω_{X/Y}`. -/
noncomputable def relativeDifferentialsBaseChangeIso :
    relativeDifferentials (pullback.snd f h) ≅
      (Modules.pullback (pullback.fst f h)).obj (relativeDifferentials f) :=
  haveI := isIso_baseChangeRelativeDifferentialsMap f h
  (asIso (baseChangeRelativeDifferentialsMap f h)).symm

end AlgebraicGeometry.Scheme
