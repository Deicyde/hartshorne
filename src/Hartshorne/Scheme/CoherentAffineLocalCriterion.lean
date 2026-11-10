/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Module.FinitePresentation
import Hartshorne.Scheme.QuasicoherentAffineLocalCriterion

/-!
# The affine-local criterion for coherence

Following Hartshorne (II.5, p. 111), an `𝒪_X`-module `F` is *coherent* when `X` has a cover
by affine opens `Uᵢ = Spec Aᵢ` such that `F|_{Uᵢ} ≅ M̃ᵢ` for finitely generated
`Aᵢ`-modules `Mᵢ`.  On a locally Noetherian scheme this is equivalent to `F` being of finite
presentation, to `F|_U` being associated to a finitely generated module on every affine open
`U = Spec A`, and to `Γ(U, F)` being a finitely generated `Γ(U, 𝒪_X)`-module with
`F|_U ≅ Γ(U, F)~` canonically on every affine open (Hartshorne II.5.4 and II.5.5).
Moreover a module `M` with `F|_U ≅ M̃` is necessarily isomorphic to `Γ(U, F)`.

The proof that finite generation on a cover gives finite generation on every affine open
does not use the Noetherian hypothesis: it compares sections on principal opens that are
principal in two affine opens at once, and descends finiteness along a finite cover of
`Spec A` by principal opens.  The Noetherian hypothesis enters only to upgrade finite
generation to finite presentation.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

/-- The restriction of an `𝒪_X`-module to an affine open `U`, viewed on `Spec Γ(X, U)`. -/
abbrev specRestriction {X : Scheme.{u}} (F : X.Modules)
    (U : X.affineOpens) : (Spec Γ(X, (U : X.Opens))).Modules :=
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  F.restrict U.2.fromSpec

/-- **Coherent module sheaves** (Hartshorne II.5, p. 111): `X` can be covered by affine opens
`Uᵢ = Spec Aᵢ` with `F|_{Uᵢ} ≅ M̃ᵢ` for finitely generated `Aᵢ`-modules `Mᵢ`. -/
def IsCoherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∃ (ι : Type u) (U : ι → X.affineOpens),
    (⨆ i, (U i : X.Opens)) = ⊤ ∧
      ∀ i, ∃ M : ModuleCat.{u} Γ(X, (U i : X.Opens)), Module.Finite Γ(X, (U i : X.Opens)) M ∧
        Nonempty ((tilde.functor Γ(X, (U i : X.Opens))).obj M ≅ specRestriction F (U i))

namespace CoherentAux

/-! ### Finiteness and changes of rings -/

theorem finite_iff_of_ringEquiv {A B N : Type*} [CommRing A] [CommRing B] [AddCommGroup N]
    [Module A N] [Module B N] (e : A ≃+* B) (h : ∀ (a : A) (n : N), a • n = e a • n) :
    Module.Finite A N ↔ Module.Finite B N := by
  let : Algebra A B := e.toRingHom.toAlgebra
  have : IsScalarTower A B N := ⟨fun a b n ↦ by
    rw [Algebra.smul_def, mul_smul, h]
    rfl⟩
  constructor
  · intro _
    exact Module.Finite.of_restrictScalars_finite A B N
  · intro _
    have : Module.Finite A B :=
      Module.Finite.of_surjective (Algebra.linearMap A B) e.surjective
    exact Module.Finite.trans B N

theorem finite_iff_of_ringEquiv_addEquiv {A B N N' : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [AddCommGroup N'] [Module A N] [Module B N'] (e : A ≃+* B) (f : N ≃+ N')
    (h : ∀ (a : A) (n : N), f (a • n) = e a • f n) :
    Module.Finite A N ↔ Module.Finite B N' := by
  let : Module A N' := Module.compHom N' e.toRingHom
  let f' : N ≃ₗ[A] N' := { f with map_smul' := h }
  rw [← finite_iff_of_ringEquiv (N := N') e (fun _ _ ↦ rfl)]
  exact ⟨fun _ ↦ Module.Finite.equiv f', fun _ ↦ Module.Finite.equiv f'.symm⟩

theorem finite_congr_opens {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : U = V) :
    Module.Finite Γ(X, U) Γ(F, U) ↔ Module.Finite Γ(X, V) Γ(F, V) := by
  subst h
  rfl

theorem finite_restrict_iff {X Y : Scheme.{u}} (h : Y ⟶ X) [IsOpenImmersion h] (F : X.Modules)
    (U : Y.Opens) :
    Module.Finite Γ(Y, U) Γ(F.restrict h, U) ↔ Module.Finite Γ(X, h ''ᵁ U) Γ(F, h ''ᵁ U) :=
  finite_iff_of_ringEquiv_addEquiv (h.appIso U).symm.commRingCatIsoToRingEquiv
    (F.restrictAppIso h U).addCommGroupIsoToAddEquiv (fun _ _ ↦ rfl)

/-! ### Localization and descent of finiteness on `Spec R` -/

variable {R : CommRingCat.{u}}

/-- A principal open of `Spec R`. -/
abbrev D (g : R) : (Spec R).Opens := PrimeSpectrum.basicOpen g

theorem finite_basicOpen_of_finite (M : (Spec R).Modules)
    (hM : IsLocalizing (modulesSpecToSheaf.obj M)) (g : R)
    [Module.Finite R Γ(M, ⊤)] :
    Module.Finite Γ(Spec R, D g) Γ(M, D g) := by
  let φ : Γ(M, ⊤) →ₗ[R] Γ(M, D g) :=
    ((modulesSpecToSheaf.obj M).obj.map (D g).leTop.op).hom
  have : IsLocalizedModule (Submonoid.powers g) φ := hM g
  exact Module.Finite.of_isLocalizedModule (Submonoid.powers g) (Rₚ := Γ(Spec R, D g)) φ

theorem finite_of_finite_basicOpen (M : (Spec R).Modules)
    (hM : IsLocalizing (modulesSpecToSheaf.obj M)) (t : Set R) (ht : Ideal.span t = ⊤)
    (H : ∀ g : t, Module.Finite Γ(Spec R, D g.1) Γ(M, D g.1)) :
    Module.Finite R Γ(M, ⊤) := by
  let φ (g : t) : Γ(M, ⊤) →ₗ[R] Γ(M, D g.1) :=
    ((modulesSpecToSheaf.obj M).obj.map (D g.1).leTop.op).hom
  have (g : t) : IsLocalizedModule (Submonoid.powers g.1) (φ g) := hM g.1
  exact Module.Finite.of_localizationSpan' t ht
    (Rₚ := fun g ↦ Γ(Spec R, D g.1)) (Mₚ := fun g ↦ Γ(M, D g.1)) φ H

/-- The ring map `Γ(X, U) → Γ(Spec Γ(X, U), ⊤) → Γ(X, U)` through `Spec` is the identity
(up to the identification of `U` with the image of `Spec Γ(X, U)`). -/
theorem ring_compat {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.map (⊤ : (Spec Γ(X, U)).Opens).leTop.op ≫
        (hU.fromSpec.appIso ⊤).inv =
      X.presheaf.map (eqToHom (hU.fromSpec.image_top_eq_opensRange.trans
        hU.opensRange_fromSpec)).op := by
  rw [← Category.assoc, Iso.comp_inv_eq, Scheme.Hom.appIso_hom, ← Category.assoc,
    Scheme.Hom.naturality, hU.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp]
  rfl

theorem map_eqToHom_map_eqToHom {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens} (h : V = W)
    (z : Γ(F, W)) : F.presheaf.map (eqToHom h.symm).op (F.presheaf.map (eqToHom h).op z) = z := by
  subst h
  simp

/-- The sections of `F` over an affine open `U` agree, as `Γ(X, U)`-modules, with the global
sections of `F|_U` on `Spec Γ(X, U)`. -/
def sectionsEquiv {X : Scheme.{u}} (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F.restrict hU.fromSpec, ⊤) where
  toFun x := (F.restrictAppIso hU.fromSpec ⊤).inv (F.presheaf.map
    (eqToHom (hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec)).op x)
  invFun y := F.presheaf.map (eqToHom (hU.fromSpec.image_top_eq_opensRange.trans
        hU.opensRange_fromSpec).symm).op ((F.restrictAppIso hU.fromSpec ⊤).hom y)
  left_inv x := by
    dsimp only
    rw [Iso.inv_hom_id_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      eqToHom_trans, eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
    rfl
  right_inv y := map_eqToHom_map_eqToHom F
    (hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec).symm y
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    have hr : (hU.fromSpec.appIso ⊤).inv ((Spec Γ(X, U)).presheaf.map
        (⊤ : (Spec Γ(X, U)).Opens).leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r)) =
        X.presheaf.map (eqToHom (hU.fromSpec.image_top_eq_opensRange.trans
          hU.opensRange_fromSpec)).op r := by
      rw [← ring_compat hU]
      rfl
    change (F.restrictAppIso hU.fromSpec ⊤).inv (F.presheaf.map _ (r • x)) =
      (F.restrictAppIso hU.fromSpec ⊤).inv (((hU.fromSpec.appIso ⊤).inv
        ((Spec Γ(X, U)).presheaf.map (⊤ : (Spec Γ(X, U)).Opens).leTop.op
          ((Scheme.ΓSpecIso Γ(X, U)).inv r))) • F.presheaf.map _ x)
    rw [hr]
    exact congrArg _ (F.val.map_smul _ r x)

end CoherentAux

open CoherentAux

/-- Finite generation of `Γ(U, F)` can be read off the sections of `F|_U` on `Spec Γ(X, U)`. -/
theorem finite_specRestriction_iff {X : Scheme.{u}} (F : X.Modules) (U : X.affineOpens) :
    Module.Finite Γ(X, (U : X.Opens)) Γ(specRestriction F U, ⊤) ↔
      Module.Finite Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens)) :=
  ⟨fun _ ↦ Module.Finite.equiv (sectionsEquiv F U.2).symm,
    fun _ ↦ Module.Finite.equiv (sectionsEquiv F U.2)⟩

/-- Finite generation of sections on an affine cover propagates to every affine open.  This is
the descent step of Hartshorne II.5.4; it does not need any Noetherian hypothesis. -/
theorem finite_of_affineCover {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} (U : ι → X.affineOpens) (hU : (⨆ i, (U i : X.Opens)) = ⊤)
    (hfin : ∀ i, Module.Finite Γ(X, (U i : X.Opens)) Γ(F, (U i : X.Opens)))
    (V : X.affineOpens) :
    Module.Finite Γ(X, (V : X.Opens)) Γ(F, (V : X.Opens)) := by
  have hloc (W : X.affineOpens) :
      IsLocalizing (modulesSpecToSheaf.obj (specRestriction F W)) := by
    let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
    rw [← isIso_fromTildeΓ_iff_isLocalizing]
    infer_instance
  have key (W : X.affineOpens) (g : Γ(X, (W : X.Opens))) :
      Module.Finite Γ(Spec Γ(X, (W : X.Opens)), D g) Γ(specRestriction F W, D g) ↔
        Module.Finite Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) := by
    let : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
    rw [finite_restrict_iff]
    exact finite_congr_opens F (W.2.fromSpec_image_basicOpen g)
  rw [← finite_specRestriction_iff]
  refine finite_of_finite_basicOpen _ (hloc V)
    {f | Module.Finite Γ(Spec Γ(X, (V : X.Opens)), D f) Γ(specRestriction F V, D f)} ?_
    (fun g ↦ g.2)
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let p : PrimeSpectrum Γ(X, (V : X.Opens)) := ⟨m, hm.isPrime⟩
  let x : X := V.2.fromSpec p
  have hxV : x ∈ (V : X.Opens) := by
    show x ∈ ((V : X.Opens) : Set X)
    rw [← V.2.range_fromSpec]
    exact ⟨p, rfl⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
  obtain ⟨g, f, hgf, hx⟩ := exists_basicOpen_le_affine_inter (U i).2 V.2 x ⟨hi, hxV⟩
  have hft : Module.Finite Γ(Spec Γ(X, (V : X.Opens)), D f) Γ(specRestriction F V, D f) := by
    rw [key, finite_congr_opens F hgf.symm, ← key]
    have : Module.Finite Γ(X, ((U i : X.affineOpens) : X.Opens))
        Γ(specRestriction F (U i), ⊤) := (finite_specRestriction_iff F (U i)).mpr (hfin i)
    exact finite_basicOpen_of_finite _ (hloc (U i)) g
  have hpf : p ∈ PrimeSpectrum.basicOpen f := by
    rw [← V.2.fromSpec_preimage_basicOpen, ← hgf]
    exact hx
  exact hpf (hle (Ideal.subset_span hft))

/-! ### Presentations -/

namespace CoherentAux

set_option backward.isDefEq.respectTransparency false in
/-- A module sheaf on `Spec R` with a presentation by finitely many generators is the tilde of
a finitely generated module. -/
theorem exists_finite_of_presentation {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (P : M.Presentation) [Finite P.generators.I] :
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧ Nonempty ((tilde.functor R).obj N ≅ M) := by
  let g := (tilde.functor _).preimage <| (tildeFinsupp _).hom ≫ P.relations.π ≫ kernel.ι _ ≫
    (tildeFinsupp _).inv
  let iso : cokernel ((tilde.functor R).map g) ≅ cokernel (P.relations.π ≫ kernel.ι _) := by
    refine cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) ?_
    simp only [g, (tilde.functor R).map_preimage]
    simp
  refine ⟨cokernel g, ?_, ⟨PreservesCokernel.iso (tilde.functor R) g ≪≫ iso ≪≫
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit⟩⟩
  exact Module.Finite.of_surjective (cokernel.π g).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

set_option backward.isDefEq.respectTransparency false in
/-- A finitely generated module over a Noetherian ring has a finite tilde presentation. -/
theorem exists_finite_presentation_tilde {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ P : (tilde M).Presentation, P.IsFinite := by
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian
    (LinearMap.ker (Finsupp.linearCombination R ((↑) : ((s : Set M)) → M)))
  refine ⟨presentationTilde M (s : Set M) hs (t : Set ((s : Set M) →₀ R)) ht, ?_⟩
  exact ⟨⟨inferInstanceAs (Finite (s : Set M))⟩,
    ⟨inferInstanceAs (Finite (t : Set ((s : Set M) →₀ R)))⟩⟩

/-- A presentation of `F|_U` on `Spec Γ(X, U)` gives a presentation of `F` over `U` with the
same generators and relations. -/
def presentationOverOfSpec {X : Scheme.{u}} (F : X.Modules) (U : X.affineOpens)
    (P : (specRestriction F U).Presentation) :
    (F.over (U : X.Opens)).Presentation := by
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let Q := Scheme.Modules.presentationRestrict U.2.isoSpec.hom P
  let e : (specRestriction F U).restrict U.2.isoSpec.hom ≅
      F.restrict (U : X.Opens).ι :=
    ((Scheme.Modules.restrictFunctorComp U.2.isoSpec.hom U.2.fromSpec).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app F
  let P' := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    e.hom e.isIso_hom Q
  let Q' := @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P'
    (Scheme.Modules.overEquiv (U : X.Opens)).inverse
    ((Scheme.Modules.overEquiv (U : X.Opens)).symm.toAdjunction.leftAdjoint_preservesColimits)
    ((U : X.Opens).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e' : F.over (U : X.Opens) ≅
      (Scheme.Modules.overEquiv (U : X.Opens)).inverse.obj
        (F.restrict (U : X.Opens).ι) :=
    (Scheme.Modules.overEquiv (U : X.Opens)).unitIso.app
      (F.over (U : X.Opens)) ≪≫
      (Scheme.Modules.overEquiv (U : X.Opens)).inverse.mapIso
        ((Scheme.Modules.overFunctorEquiv (U : X.Opens)).app F)
  letI : IsIso e'.inv := e'.isIso_inv
  exact SheafOfModules.Presentation.ofIsIso e'.inv Q'

theorem isFinite_presentationOverOfSpec {X : Scheme.{u}} (F : X.Modules) (U : X.affineOpens)
    (P : (specRestriction F U).Presentation) [P.IsFinite] :
    (presentationOverOfSpec F U P).IsFinite := by
  have h₁ : Finite P.generators.I :=
    (SheafOfModules.Presentation.IsFinite.isFiniteType_generators (p := P)).finite
  have h₂ : Finite P.relations.I :=
    (SheafOfModules.Presentation.IsFinite.isFiniteType_relations (p := P)).finite
  exact ⟨⟨inferInstanceAs (Finite P.generators.I)⟩, ⟨inferInstanceAs (Finite P.relations.I)⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- A finite presentation of `F` gives an affine open cover with presentations of the
restrictions by finitely many generators. -/
theorem exists_affineCover_presentation_finite {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] :
    ∃ (ι : Type u) (U : ι → X.Opens) (P : ∀ i, (F.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧ ∀ i, Finite (P i).generators.I := by
  obtain ⟨⟨I, W, cov, pres⟩, hfin⟩ :=
    SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  choose κ hsub heq using fun i ↦ Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (W i)
  refine ⟨Σ (i : I), κ i, fun j ↦ j.2, fun i ↦ ?_, ?_, ?_, ?_⟩
  · let u := X.homOfLE (U := i.2) (V := W i.1) (by simp [heq, le_sSup])
    have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor u) := inferInstance
    let G := (Scheme.Modules.overEquiv (W i.1)).functor ⋙ Scheme.Modules.restrictFunctor u
    let iso : SheafOfModules.overFunctor X.ringCatSheaf _ ⋙ G ≅ Scheme.Modules.restrictFunctor
      (Scheme.Opens.ι i.2.1) := (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv _) _ ≪≫
        (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (by simp [u]))
    exact SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app F).hom <|
      (pres i.1).map G (Scheme.Modules.restrictUnitIso _).symm
  · rw [Opens.coversTop_iff, IsOpenCover] at cov
    rw [IsOpenCover, iSup_sigma, ← cov]
    refine iSup_congr fun i ↦ ?_
    rw [heq i, sSup_eq_iSup']
  · intro j
    exact hsub _ j.2.2
  · intro j
    have := (hfin.isFinite_presentation j.1).isFiniteType_generators.finite
    exact this

end CoherentAux

open CoherentAux

/-- **Hartshorne II.5.4–II.5.5, uniqueness of the module.** If `F|_U ≅ M̃` on an affine open
`U = Spec A`, then necessarily `M ≅ Γ(U, F)` as `A`-modules. -/
theorem module_linearEquiv_sections_of_tilde_iso {X : Scheme.{u}} (F : X.Modules)
    (U : X.affineOpens) (M : ModuleCat.{u} Γ(X, (U : X.Opens)))
    (e : (tilde.functor Γ(X, (U : X.Opens))).obj M ≅ specRestriction F U) :
    Nonempty (M ≃ₗ[Γ(X, (U : X.Opens))] Γ(F, (U : X.Opens))) :=
  ⟨(tilde.toTildeΓNatIso.app M ≪≫ moduleSpecΓFunctor.mapIso e).toLinearEquiv.trans
    (sectionsEquiv F U.2).symm⟩

/-- Coherent `𝒪_X`-modules are quasi-coherent. -/
theorem IsCoherent.isQuasicoherent {X : Scheme.{u}} {F : X.Modules} (h : IsCoherent F) :
    F.IsQuasicoherent := by
  obtain ⟨ι, U, hU, h⟩ := h
  choose M hM e using h
  have hcov : HasAffineTildeCover F := by
    unfold HasAffineTildeCover
    exact ⟨ι, U, hU, fun i ↦ ⟨M i, e i⟩⟩
  exact ((quasicoherent_affine_local_tfae F).out 1 0).mp hcov

/-- Coherence (finite generation on an affine cover) gives finite generation of sections and
the canonical tilde description on every affine open. -/
theorem forall_affine_finite_of_isCoherent {X : Scheme.{u}} (F : X.Modules)
    (h : IsCoherent F) :
    ∀ U : X.affineOpens, Module.Finite Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens)) ∧
      IsIso (specRestriction F U).fromTildeΓ := by
  have hqc : F.IsQuasicoherent := h.isQuasicoherent
  obtain ⟨ι, U, hU, h⟩ := h
  choose M hM e using h
  have hiso := ((quasicoherent_affine_local_tfae F).out 0 2).mp hqc
  refine fun V ↦ ⟨finite_of_affineCover F U hU (fun i ↦ ?_) V, hiso V⟩
  obtain ⟨ei⟩ := module_linearEquiv_sections_of_tilde_iso F (U i) (M i) (e i).some
  exact Module.Finite.equiv ei

/-- On a locally Noetherian scheme, a module sheaf associated to finitely generated modules on
every affine open is of finite presentation. -/
theorem isFinitePresentation_of_forall_affine {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules)
    (h : ∀ U : X.affineOpens, ∃ M : ModuleCat.{u} Γ(X, (U : X.Opens)),
      Module.Finite Γ(X, (U : X.Opens)) M ∧
        Nonempty ((tilde.functor Γ(X, (U : X.Opens))).obj M ≅ specRestriction F U)) :
    F.IsFinitePresentation := by
  choose M hM e using h
  have hP (U : X.affineOpens) : ∃ P : (specRestriction F U).Presentation, P.IsFinite := by
    have : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨Q, hQ⟩ := exists_finite_presentation_tilde (M U)
    have h₁ : Finite Q.generators.I :=
      (SheafOfModules.Presentation.IsFinite.isFiniteType_generators (p := Q)).finite
    have h₂ : Finite Q.relations.I :=
      (SheafOfModules.Presentation.IsFinite.isFiniteType_relations (p := Q)).finite
    exact ⟨@SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ (e U).some.hom
      (e U).some.isIso_hom Q,
      ⟨⟨inferInstanceAs (Finite Q.generators.I)⟩, ⟨inferInstanceAs (Finite Q.relations.I)⟩⟩⟩
  choose P hP using hP
  have hcov : (Opens.grothendieckTopology X).CoversTop
      (fun U : X.affineOpens ↦ (U : X.Opens)) := by
    rw [Opens.coversTop_iff, IsOpenCover]
    exact iSup_affineOpens_eq_top X
  let σ : F.QuasicoherentData :=
    SheafOfModules.QuasicoherentData.mk.{u, u, u, u} (↥X.affineOpens)
      (fun U : X.affineOpens ↦ (U : X.Opens)) hcov (fun U ↦ presentationOverOfSpec F U (P U))
  have hσ : σ.IsFinitePresentation := by
    constructor
    intro U
    exact isFinite_presentationOverOfSpec F U (P U)
  exact SheafOfModules.IsFinitePresentation.mk.{u, u, u} ⟨σ, hσ⟩

set_option backward.isDefEq.respectTransparency false in
/-- A module sheaf of finite presentation is coherent. -/
theorem isCoherent_of_isFinitePresentation {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] : IsCoherent F := by
  obtain ⟨ι, U, P, hU, hU', hfin⟩ := exists_affineCover_presentation_finite F
  refine ⟨ι, fun i ↦ ⟨U i, hU' i⟩, hU, fun i ↦ ?_⟩
  let Q := SheafOfModules.Presentation.ofIsIso.{u, u, u}
    ((Scheme.Modules.restrictFunctorComp _ _).app F).inv
    (Scheme.Modules.presentationRestrict (hU' i).isoSpec.inv (P i))
  have : Finite Q.generators.I := hfin i
  exact exists_finite_of_presentation (specRestriction F ⟨U i, hU' i⟩) Q

/-- **Hartshorne II.5.4 (coherent clause) and II.5.5.** On a locally Noetherian scheme, for an
`𝒪_X`-module `F` the following are equivalent:

1. `F` is coherent: `F|_{Uᵢ} ≅ M̃ᵢ` with `Mᵢ` finitely generated on an affine open cover;
2. `F` is of finite presentation;
3. on every affine open `U = Spec A`, `F|_U ≅ M̃` for a finitely generated `A`-module `M`;
4. on every affine open `U`, `Γ(U, F)` is a finitely generated `Γ(U, 𝒪_X)`-module and the
   canonical map `Γ(U, F)~ → F|_U` is an isomorphism, i.e. one can take `M = Γ(U, F)`. -/
theorem coherent_affine_local_tfae {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) :
    List.TFAE
      [IsCoherent F,
        F.IsFinitePresentation,
        ∀ U : X.affineOpens, ∃ M : ModuleCat.{u} Γ(X, (U : X.Opens)),
          Module.Finite Γ(X, (U : X.Opens)) M ∧
            Nonempty ((tilde.functor Γ(X, (U : X.Opens))).obj M ≅ specRestriction F U),
        ∀ U : X.affineOpens, Module.Finite Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens)) ∧
          IsIso (specRestriction F U).fromTildeΓ] := by
  tfae_have 1 → 4 := forall_affine_finite_of_isCoherent F
  tfae_have 4 → 3 := by
    intro h U
    exact ⟨moduleSpecΓFunctor.obj (specRestriction F U),
      (finite_specRestriction_iff F U).mpr (h U).1,
      ⟨@asIso _ _ _ _ (specRestriction F U).fromTildeΓ (h U).2⟩⟩
  tfae_have 3 → 1 := fun h ↦ ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, h⟩
  tfae_have 3 → 2 := isFinitePresentation_of_forall_affine F
  tfae_have 2 → 1 := fun _ ↦ isCoherent_of_isFinitePresentation F
  tfae_finish

end

end Hartshorne
