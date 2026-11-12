/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AffineFormalGlobalSectionsExact
import Hartshorne.Scheme.AffineFormalModuleTensor
import Hartshorne.Scheme.SchemeCompletionExact

/-!
# Extensions of completed modules on an affine formal scheme

WIP
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry TensorProduct

namespace Hartshorne

universe u

section AdicComplete

variable {R : Type u} [CommRing R] (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]

/-- A finite module over a Noetherian ring that is `I`-adically complete is `I`-adically
complete. -/
theorem isAdicComplete_of_finite_of_isNoetherianRing [IsNoetherianRing R] [IsAdicComplete I R]
    [Module.Finite R M] : IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  let e₀ : R ≃ₗ[R] AdicCompletion I R :=
    LinearEquiv.ofBijective (AdicCompletion.of I R) (AdicCompletion.of_bijective I R)
  let e : M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
    (TensorProduct.lid R M).symm ≪≫ₗ TensorProduct.congr e₀ (LinearEquiv.refl R M)
  have h := (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).comp
    e.bijective
  convert h using 1
  funext x
  change AdicCompletion.of I M x = AdicCompletion.ofTensorProduct I M (e₀ 1 ⊗ₜ[R] x)
  have h1 : e₀ 1 = 1 := AdicCompletion.ext fun n => by
    rw [AdicCompletion.val_one]; rfl
  rw [h1, AdicCompletion.ofTensorProduct_tmul, one_smul]

end AdicComplete

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X) (F : X.Modules) [F.IsQuasicoherent]

/-- On an affine open `U`, the canonical map `F ⟶ i_* F̂` is bijective on sections over `U` when
`Γ(U, F)` is complete for the ideal `I(U)`. -/
theorem toModuleCompletionPushforward_app_bijective (U : X.affineOpens)
    [IsAdicComplete (I.ideal U) Γ(F, U)] :
    Function.Bijective ((I.toModuleCompletionPushforward F).val.app (op (U : X.Opens))) := by
  set V := I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)
  set T : Γ(F, U) → (I.moduleCompletion F).val.obj (op V) :=
    fun s => (I.toModuleCompletionPushforward F).val.app (op (U : X.Opens)) s with hT
  change Function.Bijective T
  have key : ∀ n (s : Γ(F, U)), (I.moduleCompletionπ F n).val.app (op V) (T s) =
        I.moduleCompletionSectionsMap F n U s := fun n s =>
    sheafOfModules_val_app_apply_of_comp_eq (I.toModuleCompletionPushforward_π F n)
      (op (U : X.Opens)) s
  have hc := isLimitOfPreserves (SheafOfModules.evaluation I.formalCompletionRingCatSheaf (op V))
    (limit.isLimit (I.moduleCompletionDiagram F))
  have htr : ∀ n x, (I.moduleCompletionMap F n).val.app (op V)
      ((I.moduleCompletionπ F (n + 1)).val.app (op V) x) =
        (I.moduleCompletionπ F n).val.app (op V) x := fun n x =>
    sheafOfModules_val_app_apply_of_comp_eq (I.moduleCompletionπ_comp_moduleCompletionMap F n)
      (op V) x
  have hext : ∀ x y : (I.moduleCompletion F).val.obj (op V),
      (∀ n, (I.moduleCompletionπ F n).val.app (op V) x =
        (I.moduleCompletionπ F n).val.app (op V) y) → x = y := by
    intro x y h
    exact Concrete.isLimit_ext _ hc x y fun ⟨n⟩ => h n
  have hmod : ∀ n (s : Γ(F, U)), I.moduleCompletionSectionsMap F n U s = 0 ↔
      s ∈ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, U)) :=
    fun n s => I.moduleCompletionSectionsMap_eq_zero_iff F n U s
  have hsub : ∀ n (a b : Γ(F, U)), I.moduleCompletionSectionsMap F n U a =
      I.moduleCompletionSectionsMap F n U b ↔
        a - b ∈ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, U)) := by
    intro n a b
    rw [← hmod n (a - b), map_sub, sub_eq_zero]
  constructor
  · intro a b hab
    rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := I.ideal U) (M := Γ(F, U)) inferInstance (a - b) fun n => ?_
    refine (SModEq.zero (M := Γ(F, U)) (x := a - b)).2 ?_
    cases n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial
    | succ n => rw [← hsub, ← key, ← key, hab]
  · intro t
    have hsurj := fun n => I.moduleCompletionSectionsMap_surjective F n U
    choose s hs using fun n => hsurj n ((I.moduleCompletionπ F n).val.app (op V) t)
    have hstep : ∀ n, s (n + 1) - s n ∈
        I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, U)) := by
      intro n
      rw [← hsub, hs n, ← key, ← htr, key, hs (n + 1), htr]
    have hle : ∀ m n, m ≤ n → s n - s m ∈
        I.ideal U ^ (m + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, U)) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have h2 := Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega : m + 1 ≤ n + 1))
          (hstep n)
        have := Submodule.add_mem _ h2 ih
        rwa [sub_add_sub_cancel] at this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I.ideal U) (M := Γ(F, U)) inferInstance (f := s)
      fun {m n} hmn => by
        rw [SModEq.sub_mem, ← neg_mem_iff, neg_sub]
        exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ m)) (hle m n hmn)
    refine ⟨L, hext _ _ fun n => ?_⟩
    refine (key n L).trans (((hsub n L (s n)).2 ?_).trans (hs n))
    have h1 := hL (n + 1)
    rw [SModEq.sub_mem] at h1
    have h2 := hstep n
    have := Submodule.sub_mem _ h1 h2
    rwa [sub_sub_sub_cancel_left, ← neg_sub, neg_mem_iff] at this

end QuasicoherentIdealSubsheaf


section RingEquiv

/-- Adic completeness transports along a ring isomorphism `e : B ≃+* C`: if `C` is complete for
`I`, then `B` is complete for the preimage of `I`. -/
theorem isAdicComplete_comap_ringEquiv {B C : Type u} [CommRing B] [CommRing C] (e : B ≃+* C)
    (I : Ideal C) [IsAdicComplete I C] : IsAdicComplete (I.comap e) B := by
  have key : ∀ (n : ℕ) (x : B), x ∈ (I.comap e) ^ n • (⊤ : Submodule B B) ↔
      e x ∈ I ^ n • (⊤ : Submodule C C) := by
    intro n x
    simp only [smul_eq_mul, Ideal.mul_top]
    rw [← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  have hmod : ∀ (n : ℕ) (x y : B), x ≡ y [SMOD (I.comap e) ^ n • (⊤ : Submodule B B)] ↔
      e x ≡ e y [SMOD I ^ n • (⊤ : Submodule C C)] := by
    intro n x y
    rw [SModEq.sub_mem, SModEq.sub_mem, key, map_sub]
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · refine e.injective ((IsHausdorff.haus (I := I) (M := C) inferInstance (e x) fun n => ?_).trans
      (map_zero e).symm)
    rw [← map_zero e]
    exact (hmod n x 0).1 (hx n)
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := C) inferInstance (f := fun n => e (f n))
      fun {m n} hmn => (hmod m _ _).1 (hf hmn)
    refine ⟨e.symm L, fun n => (hmod n _ _).2 ?_⟩
    rw [RingEquiv.apply_symm_apply]
    exact hL n

end RingEquiv

section Affine

variable {A : CommRingCat.{u}} (I : Ideal A)

/-- The kernel of `Γ(Spec A, 𝒪) → Γ(Spec (A ⧸ I), 𝒪)` is `I`, read in `Γ(Spec A, 𝒪) ≅ A`. -/
private lemma ker_appTop_spec_map_quotient_mk_aux :
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom =
      I.comap (Scheme.ΓSpecIso A).hom.hom := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).hom.hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).hom)).1
  rw [← RingHom.ker_comp_of_injective _ hinj, ← CommRingCat.hom_comp, h, CommRingCat.hom_comp,
    ← RingHom.comap_ker, CommRingCat.hom_ofHom, Ideal.mk_ker]
  rfl

/-- The global ideal of the ideal sheaf attached to `I ⊆ A` is `I`, read in
`Γ(Spec A, 𝒪) ≅ A`. -/
theorem specIdealSubsheaf_ideal_top :
    (specIdealSubsheaf A I).ideal ⊤ = I.comap (Scheme.ΓSpecIso A).hom.hom := by
  have h1 : RingHom.ker (((specIdealSubsheaf A I).infinitesimalNeighborhoodι 1).app ⊤).hom =
      (specIdealSubsheaf A I).ideal ⊤ ^ 1 :=
    (Scheme.IdealSheafData.ker_subschemeι_app _ ⟨⊤, isAffineOpen_top _⟩).trans
      ((specIdealSubsheaf A I).ideal_pow 1 ⟨⊤, isAffineOpen_top _⟩)
  rw [pow_one] at h1
  refine h1.symm.trans ?_
  rw [← specIdealSubsheafNeighborhoodOneIso_hom_comp]
  change RingHom.ker (Scheme.Hom.appTop _).hom = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.ker_comp_of_injective]
  · exact ker_appTop_spec_map_quotient_mk_aux I
  · exact (ConcreteCategory.bijective_of_isIso
      ((specIdealSubsheafNeighborhoodOneIso A I).hom.app ⊤)).1


variable [IsNoetherianRing A]

/-- For `A` Noetherian and `I`-adically complete and `N` a finite `A`-module, the global sections
`Γ(Spec A, N~)` are complete for the global ideal of the ideal sheaf attached to `I`. -/
theorem isAdicComplete_tilde_top [IsAdicComplete I A] (N : ModuleCat.{u} A) [Module.Finite A N] :
    IsAdicComplete ((specIdealSubsheaf A I).ideal ⊤) Γ(tilde N, ⊤) := by
  rw [specIdealSubsheaf_ideal_top]
  let e := (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv
  have : IsAdicComplete (I.comap (Scheme.ΓSpecIso A).hom.hom) Γ(Spec A, ⊤) :=
    isAdicComplete_comap_ringEquiv e I
  have : IsNoetherianRing Γ(Spec A, ⊤) := isNoetherianRing_of_ringEquiv _ e.symm
  have : Module.Finite A Γ(tilde N, ⊤) := Module.Finite.equiv (tilde.isoTop N).toLinearEquiv
  have : Module.Finite Γ(Spec A, ⊤) Γ(tilde N, ⊤) :=
    Module.Finite.of_restrictScalars_finite A _ _
  exact isAdicComplete_of_finite_of_isNoetherianRing _ _

/-- **The adjunction `M ↦ (M~)|_{V(I)} ⊗ 𝒪_X̂` ⊣ `Γ(X̂, -)`** between `A`-modules and modules over
the structure sheaf of `X̂ = Spf_I(A)`: the composite of `M ↦ M~` ⊣ `Γ(Spec A, -)` and the module
pullback along `X̂ ⟶ Spec A` ⊣ pushforward. The right adjoint sends `F` to `Γ(X̂, F)`, an
`A`-module through `A ⟶ Γ(X̂, 𝒪_X̂)`. -/
def affineFormalTildeAdjunction :
    tilde.functor A ⋙ SheafOfModules.pullback.{u}
        (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat ⊣
      SheafOfModules.pushforward.{u} (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat
        ⋙ moduleSpecΓFunctor :=
  tilde.adjunction.comp (SheafOfModules.pullbackPushforwardAdjunction.{u}
    (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat)

/-- For `A` Noetherian and `I`-adically complete and `N` a finite `A`-module, the unit
`N ⟶ Γ(X̂, (N~)|_{V(I)} ⊗ 𝒪_X̂)` is an isomorphism: global sections recover `N` from its
completion. -/
theorem isIso_affineFormalTildeAdjunction_unit_app [IsAdicComplete I A] (N : ModuleCat.{u} A)
    [Module.Finite A N] : IsIso ((affineFormalTildeAdjunction I).unit.app N) := by
  have e : (affineFormalTildeAdjunction I).unit.app N = tilde.adjunction.unit.app N ≫
      moduleSpecΓFunctor.map ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat).unit.app (tilde N)) :=
    Adjunction.comp_unit_app _ _ N
  rw [e]
  suffices hs : IsIso (moduleSpecΓFunctor.map ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat).unit.app (tilde N))) from
    have := NatIso.isIso_app_of_isIso (tilde.adjunction (R := A)).unit N
    @IsIso.comp_isIso _ _ _ _ _ _ _ this hs
  have hc := isIso_tildePullbackToModuleCompletion I N
  have h := ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat).homEquiv_unit _ _
      ((specIdealSubsheaf A I).pullbackToModuleCompletion (tilde N))).symm.trans
    (Equiv.apply_symm_apply _ ((specIdealSubsheaf A I).toModuleCompletionPushforward (tilde N)))
  have hT : IsIso (moduleSpecΓFunctor.map
      ((specIdealSubsheaf A I).toModuleCompletionPushforward (tilde N))) := by
    have := isAdicComplete_tilde_top I N
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (specIdealSubsheaf A I).toModuleCompletionPushforward_app_bijective (tilde N)
      ⟨⊤, isAffineOpen_top _⟩
  rw [← h] at hT
  erw [Functor.map_comp] at hT
  have h2 : IsIso (moduleSpecΓFunctor.map ((SheafOfModules.pushforward.{u}
      (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat).map
        ((specIdealSubsheaf A I).pullbackToModuleCompletion (tilde N)))) :=
    ((moduleSpecΓFunctor (R := A)).mapIso ((SheafOfModules.pushforward.{u}
      (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat).mapIso
        (asIso ((specIdealSubsheaf A I).pullbackToModuleCompletion (tilde N))))).isIso_hom
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 hT


/-- For `A` Noetherian and `N` a finite `A`-module, `N~` is coherent on `Spec A`. -/
theorem isCoherent_tilde_of_finite (N : ModuleCat.{u} A) [Module.Finite A N] :
    IsCoherent (tilde N) := by
  obtain ⟨Q, hQ⟩ := CoherentAux.exists_finite_presentation_tilde N
  have h₁ : Finite Q.generators.I :=
    (SheafOfModules.Presentation.IsFinite.isFiniteType_generators (p := Q)).finite
  have h₂ : Finite Q.relations.I :=
    (SheafOfModules.Presentation.IsFinite.isFiniteType_relations (p := Q)).finite
  have hσ : Q.quasicoherentData.IsFinitePresentation := by
    constructor
    intro x
    exact ⟨⟨inferInstanceAs (Finite Q.generators.I)⟩, ⟨inferInstanceAs (Finite Q.relations.I)⟩⟩
  have : (tilde N).IsFinitePresentation :=
    SheafOfModules.IsFinitePresentation.mk.{u, u, u} ⟨Q.quasicoherentData, hσ⟩
  exact isCoherent_of_isFinitePresentation _

/-- For `A` Noetherian and `I`-adically complete and `N` a finite `A`-module, the counit
`(Γ(X̂, F)~)|_{V(I)} ⊗ 𝒪_X̂ ⟶ F` is an isomorphism at `F = (N~)|_{V(I)} ⊗ 𝒪_X̂`. -/
theorem isIso_affineFormalTildeAdjunction_counit_app [IsAdicComplete I A] (N : ModuleCat.{u} A)
    [Module.Finite A N] :
    IsIso ((affineFormalTildeAdjunction I).counit.app
      ((tilde.functor A ⋙ SheafOfModules.pullback.{u}
        (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat).obj N)) := by
  have := isIso_affineFormalTildeAdjunction_unit_app I N
  exact IsIso.of_isIso_fac_left ((affineFormalTildeAdjunction I).left_triangle_components N)


/-- **Extensions of completed finite modules on an affine formal scheme.** Let `A` be a Noetherian
ring, complete for an ideal `I`, and `X̂ = Spf_I(A)`. Let `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` be a short exact
sequence of `𝒪_X̂`-modules with `F' ≅ (M'~)^` and `F'' ≅ (M''~)^` for finite `A`-modules `M'`,
`M''`. Then `M = Γ(X̂, F)` is a finite `A`-module and `F ≅ (M~)^`. -/
theorem affineFormal_extension_moduleCompletion [IsAdicComplete I A]
    {S : ShortComplex (SheafOfModules.{u} (specIdealSubsheaf A I).formalCompletionRingCatSheaf)}
    (hS : S.ShortExact) (M' M'' : ModuleCat.{u} A) [Module.Finite A M'] [Module.Finite A M'']
    (e₁ : S.X₁ ≅ (specIdealSubsheaf A I).moduleCompletion (tilde M'))
    (e₃ : S.X₃ ≅ (specIdealSubsheaf A I).moduleCompletion (tilde M'')) :
    ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
      Nonempty (S.X₂ ≅ (specIdealSubsheaf A I).moduleCompletion (tilde M)) := by
  let adj := affineFormalTildeAdjunction I
  let L := tilde.functor A ⋙ SheafOfModules.pullback.{u}
    (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat
  let R := SheafOfModules.pushforward.{u}
    (specIdealSubsheaf A I).structureSheafToFormalCompletionRingCat ⋙ moduleSpecΓFunctor
  have hε : ∀ (F : SheafOfModules.{u} (specIdealSubsheaf A I).formalCompletionRingCatSheaf)
      (N : ModuleCat.{u} A) [Module.Finite A N],
      (F ≅ (specIdealSubsheaf A I).moduleCompletion (tilde N)) → IsIso (adj.counit.app F) := by
    intro F N _ e
    have := isIso_affineFormalTildeAdjunction_counit_app I N
    exact (NatTrans.isIso_app_iff_of_iso adj.counit
      (e ≪≫ (tildePullbackIsoModuleCompletion I N).symm)).2 this
  have : R.IsRightAdjoint := adj.isRightAdjoint
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have hR : ∀ (F : SheafOfModules.{u} (specIdealSubsheaf A I).formalCompletionRingCatSheaf)
      (N : ModuleCat.{u} A) [Module.Finite A N],
      (F ≅ (specIdealSubsheaf A I).moduleCompletion (tilde N)) → Nonempty (R.obj F ≅ N) := by
    intro F N _ e
    have := isIso_affineFormalTildeAdjunction_unit_app I N
    exact ⟨R.mapIso (e ≪≫ (tildePullbackIsoModuleCompletion I N).symm) ≪≫
      (asIso (adj.unit.app N)).symm⟩
  have hRS : (S.map R).ShortExact := by
    have hcoh : IsCoherentFormalModule (X := (specIdealSubsheaf A I).toNoetherianFormalScheme)
        S.X₁ :=
      ((specIdealSubsheaf A I).isCoherentFormalModule_moduleCompletion (tilde M')
        (isCoherent_tilde_of_finite M')).of_iso e₁.symm
    have h := affineFormal_globalSections_shortExact (isAffineNoetherianFormalScheme_Spf A I) hS
      hcoh
    have hinj := (ModuleCat.mono_iff_injective _).1 h.mono_f
    have hsurj := (ModuleCat.epi_iff_surjective _).1 h.epi_g
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h.exact
    exact
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hex
        mono_f := (ModuleCat.mono_iff_injective _).2 hinj
        epi_g := (ModuleCat.epi_iff_surjective _).2 hsurj }
  have f₁ : Module.Finite A (S.map R).X₁ :=
    Module.Finite.equiv (hR _ M' e₁).some.toLinearEquiv.symm
  have f₃ : Module.Finite A (S.map R).X₃ :=
    Module.Finite.equiv (hR _ M'' e₃).some.toLinearEquiv.symm
  have f₂ : Module.Finite A (R.obj S.X₂) :=
    Module.Finite.of_exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      hRS.exact) ((ModuleCat.epi_iff_surjective _).mp hRS.epi_g)
  have hLRS : ((S.map R).map L).ShortExact := by
    have f₂' : Module.Finite A (S.map R).X₂ := f₂
    have h := moduleCompletion_tilde_shortExact I (S.map R) hRS
    let c := tildePullbackToModuleCompletion I
    have hc : ∀ (N : ModuleCat.{u} A) [Module.Finite A N], IsIso (c.app N) :=
      fun N _ => isIso_tildePullbackToModuleCompletion I N
    refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk
      (@asIso _ _ _ _ (c.app _) (hc _)) (@asIso _ _ _ _ (c.app _) (hc _))
      (@asIso _ _ _ _ (c.app _) (hc _)) (c.naturality _).symm (c.naturality _).symm).symm h
  let φ : (S.map R).map L ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  have : IsIso φ.τ₁ := hε _ M' e₁
  have : IsIso φ.τ₃ := hε _ M'' e₃
  have : IsIso φ.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hLRS hS
  exact ⟨R.obj S.X₂, f₂, ⟨(asIso φ.τ₂).symm ≪≫
    tildePullbackIsoModuleCompletion I (R.obj S.X₂)⟩⟩


/-- On `X̂ = Spf_I(A)` with `A` Noetherian and `I`-adically complete, an extension of `(M''~)^` by
`(M'~)^`, for finite `A`-modules `M'` and `M''`, is a coherent module on the Noetherian formal
scheme `X̂`. -/
theorem affineFormal_extension_isCoherentFormalModule [IsAdicComplete I A]
    {S : ShortComplex (SheafOfModules.{u} (structureRingCatSheaf
      (specIdealSubsheaf A I).toNoetherianFormalScheme.toLocallyRingedSpace))}
    (hS : S.ShortExact) (M' M'' : ModuleCat.{u} A) [Module.Finite A M'] [Module.Finite A M'']
    (e₁ : S.X₁ ≅ (specIdealSubsheaf A I).moduleCompletion (tilde M'))
    (e₃ : S.X₃ ≅ (specIdealSubsheaf A I).moduleCompletion (tilde M'')) :
    IsCoherentFormalModule S.X₂ := by
  obtain ⟨M, hM, ⟨e⟩⟩ := affineFormal_extension_moduleCompletion I hS M' M'' e₁ e₃
  exact ((specIdealSubsheaf A I).isCoherentFormalModule_moduleCompletion (tilde M)
    (isCoherent_tilde_of_finite M)).of_iso e.symm

end Affine

end Hartshorne
