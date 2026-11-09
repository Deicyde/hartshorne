/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Hartshorne.Scheme.LocallyFreeInvertible
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.LocalProperties.Projective

/-!
# The free locus of a coherent sheaf

Hartshorne, *Algebraic Geometry*, Exercise II.5.7(a,b) (p. 124).

Let `X` be a Noetherian scheme and `F` a coherent `𝒪_X`-module. If the stalk `F_x` is a free
`𝒪_{X,x}`-module, then `F` is free on an open neighbourhood of `x`; consequently `F` is locally
free if and only if all of its stalks are free.

Coherence and (local) freeness are the project notions `Hartshorne.IsCoherent` and
`AlgebraicGeometry.Scheme.Modules.IsFree` / `IsLocallyFree`.  The stalk `F_x` carries its
`𝒪_{X,x}`-module structure from Mathlib's `PresheafOfModules` stalk API.

The proof works on an affine open `V = Spec A` containing `x`, where `F|_V ≅ M̃` with
`M = Γ(V, F)` finitely presented (as `A` is Noetherian):

* freeness of a stalk is invariant under restriction along an open immersion
  (`free_stalk_restrict_iff`), so `F_x` free means `(M̃)_𝔭` free over `𝒪_{Spec A, 𝔭}`;
* for a quasi-coherent module on `Spec A` the germ map `Γ(Spec A, G) → G_𝔭` is a localization
  at `𝔭` (`isLocalizedModule_germTopLinear`), so `M_𝔭` is free;
* a basis of `M_𝔭` spreads out to a basis of `M_r` for some `r ∉ 𝔭` (Mathlib's
  `Module.FinitePresentation.exists_free_localizedModule_powers`), hence `Γ(D(r), F)` is free;
* a quasi-coherent module with free sections on an affine open is free there
  (`isFree_restrict_of_free_sections`).

Conversely the stalks of a free module sheaf on an affine scheme are localizations of a free
module, hence free, and this gives the stalks of any locally free module.  The Noetherian
hypothesis is only used through local Noetherianity, and the results are also stated in that
generality.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

/-- The stalk `F_x` of an `𝒪_X`-module is a module over the local ring `𝒪_{X,x}`. -/
instance schemeModulesStalkModule {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  inferInstanceAs (Module (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x))

/-- Germs are compatible with the module structures on sections and stalks. -/
theorem schemeModules_germ_smul {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (x : X)
    (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(F, U)) :
    F.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  PresheafOfModules.germ_smul M x U hx r m

namespace FreeLocusAux

variable {R : CommRingCat.{u}}

/-- The `R`-algebra structure on the local ring of `Spec R` at a point. -/
abbrev freeLocusStalkAlgebra (y : Spec R) : Algebra R ((Spec R).presheaf.stalk y) :=
  StructureSheaf.stalkAlgebra R y

attribute [local instance] freeLocusStalkAlgebra

theorem freeLocus_asIdeal_isPrime (y : Spec R) : y.asIdeal.IsPrime :=
  PrimeSpectrum.isPrime (R := R) y

attribute [local instance] freeLocus_asIdeal_isPrime

theorem freeLocus_stalk_isLocalization (y : Spec R) :
    IsLocalization.AtPrime ((Spec R).presheaf.stalk y) y.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk R y

attribute [local instance] freeLocus_stalk_isLocalization

/-- The `R`-module structure on a stalk of an `𝒪_{Spec R}`-module. -/
abbrev freeLocusStalkModule (G : (Spec R).Modules) (y : Spec R) :
    Module R (G.presheaf.stalk y) :=
  Module.compHom _ (algebraMap R ((Spec R).presheaf.stalk y))

attribute [local instance] freeLocusStalkModule

theorem freeLocus_stalk_isScalarTower (G : (Spec R).Modules) (y : Spec R) :
    IsScalarTower R ((Spec R).presheaf.stalk y) (G.presheaf.stalk y) :=
  IsScalarTower.of_compHom R _ _

attribute [local instance] freeLocus_stalk_isScalarTower

theorem germ_smul_spec (G : (Spec R).Modules) (y : Spec R) (U : (Spec R).Opens) (hy : y ∈ U)
    (r : R) (s : Γ(G, U)) :
    G.presheaf.germ U y hy (r • s) = r • G.presheaf.germ U y hy s := by
  change G.presheaf.germ U y hy
      (((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r)) • s) = _
  rw [schemeModules_germ_smul]
  change _ = (Spec R).presheaf.germ ⊤ y trivial ((Scheme.ΓSpecIso R).inv r) •
    G.presheaf.germ U y hy s
  rw [TopCat.Presheaf.germ_res_apply]

/-- The germ map from global sections to a stalk, as an `R`-linear map. -/
def germTopLinear (G : (Spec R).Modules) (y : Spec R) :
    Γ(G, ⊤) →ₗ[R] G.presheaf.stalk y where
  toFun := G.presheaf.germ ⊤ y trivial
  map_add' := map_add _
  map_smul' := germ_smul_spec G y ⊤ trivial

theorem isLocalizedModule_germTopLinear (G : (Spec R).Modules)
    (hG : IsLocalizing (modulesSpecToSheaf.obj G)) (y : Spec R) :
    IsLocalizedModule y.asIdeal.primeCompl (germTopLinear G y) where
  map_units s := by
    obtain ⟨u, hu⟩ := IsLocalization.map_units ((Spec R).presheaf.stalk y) s
    rw [Module.End.isUnit_iff]
    have key (m : G.presheaf.stalk y) :
        algebraMap R (Module.End R (G.presheaf.stalk y)) s m = (u : (Spec R).presheaf.stalk y) • m := by
      rw [hu]
      rfl
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun m ↦ ((u⁻¹ : ((Spec R).presheaf.stalk y)ˣ) : (Spec R).presheaf.stalk y) • m,
        fun m ↦ ?_, fun m ↦ ?_⟩
    · simp only [key, smul_smul, Units.inv_mul, one_smul]
    · simp only [key, smul_smul, Units.mul_inv, one_smul]
  surj z := by
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf z
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hyg, hgU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hU U.2
    have hgU' : CoherentAux.D g ≤ U := hgU
    have hyg' : y ∈ CoherentAux.D g := hyg
    obtain ⟨⟨m, ⟨c, hc⟩⟩, hm⟩ := (hG g).surj (G.presheaf.map (homOfLE hgU').op s)
    obtain ⟨n, rfl⟩ := hc
    have hm' : g ^ n • G.presheaf.map (homOfLE hgU').op s =
        G.presheaf.map (CoherentAux.D g).leTop.op m := hm
    refine ⟨⟨m, ⟨g ^ n, fun h ↦ hyg (y.isPrime.mem_of_pow_mem n h)⟩⟩, ?_⟩
    change g ^ n • G.presheaf.germ U y hU s = G.presheaf.germ ⊤ y trivial m
    rw [← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE hgU') y hyg',
      ← germ_smul_spec G y (CoherentAux.D g) hyg', hm']
    exact TopCat.Presheaf.germ_res_apply G.presheaf (CoherentAux.D g).leTop y hyg' (m : Γ(G, ⊤))
  exists_of_eq {m₁ m₂} h := by
    obtain ⟨W, hW, i₁, i₂, hi⟩ :=
      TopCat.Presheaf.germ_eq G.presheaf (U := ⊤) (V := ⊤) y trivial trivial m₁ m₂ h
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hyg, hgW⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hW W.2
    have hgW' : CoherentAux.D g ≤ W := hgW
    have hρ : (modulesSpecToSheaf.obj G).obj.map (PrimeSpectrum.basicOpen g).leTop.op m₁ =
        (modulesSpecToSheaf.obj G).obj.map (PrimeSpectrum.basicOpen g).leTop.op m₂ := by
      change G.presheaf.map (CoherentAux.D g).leTop.op m₁ =
        G.presheaf.map (CoherentAux.D g).leTop.op m₂
      calc G.presheaf.map (CoherentAux.D g).leTop.op m₁
          = G.presheaf.map (homOfLE hgW').op (G.presheaf.map i₁.op m₁) := by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
        _ = G.presheaf.map (homOfLE hgW').op (G.presheaf.map i₂.op m₂) := by rw [hi]
        _ = G.presheaf.map (CoherentAux.D g).leTop.op m₂ := by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    obtain ⟨⟨c, hc⟩, hcm⟩ := (hG g).exists_of_eq hρ
    obtain ⟨n, rfl⟩ := hc
    exact ⟨⟨g ^ n, fun h ↦ hyg (y.isPrime.mem_of_pow_mem n h)⟩, hcm⟩

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Freeness of the localization transfers along any presentation of the localization. -/
theorem free_of_isLocalizedModule_of_free_localization {R : Type*} [CommRing R] (S : Submonoid R) {M M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')
    [IsLocalizedModule S f] (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    [Module Rₛ M'] [IsScalarTower R Rₛ M']
    [Module.Free (Localization S) (LocalizedModule S M)] : Module.Free Rₛ M' := by
  set e := (IsLocalization.algEquiv S (Localization S) Rₛ).toRingEquiv
  refine (Module.Free.iff_of_equiv (σ := (e : Localization S →+* Rₛ)) (M := LocalizedModule S M) (M' := M') ?_).mp
    inferInstance
  refine { __ := IsLocalizedModule.iso S f, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp [e, ← map_smul, ← smul_assoc]


variable {X : Scheme.{u}}

theorem isFree_restrict_comp {Y Z : Scheme.{u}} (F : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (g : Z ⟶ Y) [IsOpenImmersion g] (h : (F.restrict f).IsFree) :
    (F.restrict (g ≫ f)).IsFree := by
  obtain ⟨I, ⟨α⟩⟩ := h
  exact ⟨I, ⟨(Scheme.Modules.restrictFunctorComp g f).app F ≪≫
    (Scheme.Modules.restrictFunctor g).mapIso α ≪≫ Scheme.Modules.restrictFreeIso g I⟩⟩

theorem isFree_restrict_congr {Y : Scheme.{u}} (F : X.Modules) {f g : Y ⟶ X} (hfg : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (h : (F.restrict f).IsFree) :
    (F.restrict g).IsFree := by
  obtain ⟨I, ⟨α⟩⟩ := h
  exact ⟨I, ⟨(Scheme.Modules.restrictFunctorCongr hfg).symm.app F ≪≫ α⟩⟩

/-- If `F` is associated on an affine open `W` to its sections, and these sections are free,
then `F` is free on `W`. -/
theorem isFree_restrict_of_free_sections (F : X.Modules) (W : X.affineOpens)
    [IsIso (specRestriction F W).fromTildeΓ]
    [Module.Free Γ(X, (W : X.Opens)) Γ(F, (W : X.Opens))] :
    (F.restrict (W : X.Opens).ι).IsFree := by
  let A := Γ(X, (W : X.Opens))
  let I := Module.Free.ChooseBasisIndex A Γ(F, (W : X.Opens))
  let b := Module.Free.chooseBasis A Γ(F, (W : X.Opens))
  let e : moduleSpecΓFunctor.obj (specRestriction F W) ≅ ModuleCat.of A (I →₀ A) :=
    ((CoherentAux.sectionsEquiv F W.2).symm ≪≫ₗ b.repr).toModuleIso
  have hfree : (specRestriction F W).IsFree :=
    ⟨I, ⟨(asIso (specRestriction F W).fromTildeΓ).symm ≪≫ (tilde.functor A).mapIso e ≪≫
      tildeFinsupp I⟩⟩
  have : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  exact isFree_restrict_congr F W.2.isoSpec_hom_fromSpec
    (isFree_restrict_comp F W.2.fromSpec W.2.isoSpec.hom hfree)


/-- To check a property of pairs of a scalar and an element of a stalk, it suffices to check it
on germs over a common open neighbourhood. -/
theorem stalk_smul_induction {M : X.Modules} (x : X)
    {P : X.presheaf.stalk x → M.presheaf.stalk x → Prop}
    (h : ∀ (U : X.Opens) (hx : x ∈ U) (t : Γ(X, U)) (s : Γ(M, U)),
      P (X.presheaf.germ U x hx t) (M.presheaf.germ U x hx s))
    (r : X.presheaf.stalk x) (m : M.presheaf.stalk x) : P r m := by
  obtain ⟨U₁, h₁, t, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨U₂, h₂, s, rfl⟩ := M.presheaf.exists_germ_eq m
  have hx : x ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hx,
    ← M.presheaf.germ_res_apply (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) x hx]
  exact h _ hx _ _

/-- The additive isomorphism between the stalk of a restriction along an open immersion and the
stalk at the image point. -/
def restrictStalkIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) (y : Y) :
    (M.restrict f).presheaf.stalk y ≅ M.presheaf.stalk (f y) :=
  (Scheme.Modules.restrictStalkNatIso f y).app M

theorem restrictStalkIso_hom_germ {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (y : Y) (U : Y.Opens) (hy : y ∈ U) (hfy : f y ∈ f ''ᵁ U)
    (s : Γ(M.restrict f, U)) :
    (restrictStalkIso f M y).hom ((M.restrict f).presheaf.germ U y hy s) =
      M.presheaf.germ (f ''ᵁ U) (f y) hfy s := by
  rw [restrictStalkIso, ← ConcreteCategory.comp_apply]
  exact congr($(Scheme.Modules.germ_restrictStalkNatIso_hom_app f y M hy) s)

/-- The ring isomorphism `𝒪_{X,f(y)} ≅ 𝒪_{Y,y}` for an open immersion `f`. -/
def stalkRingEquiv {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    X.presheaf.stalk (f y) ≃+* Y.presheaf.stalk y :=
  (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv

theorem stalkRingEquiv_symm_germ {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y)
    (U : Y.Opens) (hy : y ∈ U) (hfy : f y ∈ f ''ᵁ U) (t : Γ(Y, U)) :
    (stalkRingEquiv f y).symm (Y.presheaf.germ U y hy t) =
      X.presheaf.germ (f ''ᵁ U) (f y) hfy ((f.appIso U).inv t) := by
  rw [RingEquiv.symm_apply_eq]
  change _ = f.stalkMap y _
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
  exact (TopCat.Presheaf.germ_res_apply Y.presheaf _ y hfy t).symm

theorem restrictStalkIso_hom_smul {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (y : Y) (b : Y.presheaf.stalk y) (n : (M.restrict f).presheaf.stalk y) :
    (restrictStalkIso f M y).hom (b • n) =
      (stalkRingEquiv f y).symm b • (restrictStalkIso f M y).hom n := by
  induction b, n using stalk_smul_induction y with
  | h U hy t s =>
    have hfy : f y ∈ f ''ᵁ U := Set.mem_image_of_mem _ hy
    rw [← schemeModules_germ_smul, restrictStalkIso_hom_germ f M y U hy hfy,
      restrictStalkIso_hom_germ f M y U hy hfy, stalkRingEquiv_symm_germ f y U hy hfy]
    exact schemeModules_germ_smul M (f ''ᵁ U) (f y) hfy ((f.appIso U).inv t) s

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Freeness of a stalk can be computed after restricting along an open immersion. -/
theorem free_stalk_restrict_iff {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (y : Y) :
    Module.Free (X.presheaf.stalk (f y)) (M.presheaf.stalk (f y)) ↔
      Module.Free (Y.presheaf.stalk y) ((M.restrict f).presheaf.stalk y) := by
  let φ := restrictStalkIso f M y
  let σ := stalkRingEquiv f y
  refine Module.Free.iff_of_equiv (σ := (σ : X.presheaf.stalk (f y) →+* Y.presheaf.stalk y))
    { toFun := φ.inv
      invFun := φ.hom
      left_inv := φ.inv_hom_id_apply
      right_inv := φ.hom_inv_id_apply
      map_add' := map_add _
      map_smul' := fun a m ↦ ?_ }
  change φ.inv (a • m) = σ a • φ.inv m
  calc φ.inv (a • m) = φ.inv (φ.hom (σ a • φ.inv m)) := by
        rw [restrictStalkIso_hom_smul, RingEquiv.symm_apply_apply, φ.inv_hom_id_apply]
    _ = σ a • φ.inv m := φ.hom_inv_id_apply _

theorem isFree_restrict_comp_of_restrict {Y Z : Scheme.{u}} (F : X.Modules) (f : Y ⟶ X)
    [IsOpenImmersion f] (g : Z ⟶ Y) [IsOpenImmersion g] (h : ((F.restrict f).restrict g).IsFree) :
    (F.restrict (g ≫ f)).IsFree := by
  obtain ⟨I, ⟨α⟩⟩ := h
  exact ⟨I, ⟨(Scheme.Modules.restrictFunctorComp g f).app F ≪≫ α⟩⟩

end FreeLocusAux

open FreeLocusAux

attribute [local instance] freeLocusStalkAlgebra freeLocus_asIdeal_isPrime
  freeLocus_stalk_isLocalization freeLocusStalkModule freeLocus_stalk_isScalarTower

/-- The stalks of a free module sheaf on an affine scheme are free. -/
theorem free_stalk_free_spec {R : CommRingCat.{u}} (I : Type u) (G : (Spec R).Modules)
    (hG : G ≅ SheafOfModules.free I) (y : Spec R) :
    Module.Free ((Spec R).presheaf.stalk y) (G.presheaf.stalk y) := by
  have : IsIso (Scheme.Modules.fromTildeΓ (R := R) G) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeFinsupp I ≪≫ hG.symm⟩⟩
  have hloc : IsLocalizing (modulesSpecToSheaf.obj G) :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mp this
  have := isLocalizedModule_germTopLinear G hloc y
  let e : Γ(G, ⊤) ≃ₗ[R] (I →₀ R) :=
    (moduleSpecΓFunctor.mapIso (hG ≪≫ (tildeFinsupp I).symm) ≪≫
      (tilde.toTildeΓNatIso.app (ModuleCat.of R (I →₀ R))).symm).toLinearEquiv
  have : Module.Free R Γ(G, ⊤) := Module.Free.of_equiv e.symm
  exact Module.free_of_isLocalizedModule y.asIdeal.primeCompl (germTopLinear G y)

/-- The stalks of a locally free module sheaf are free. -/
theorem free_stalk_of_isLocallyFree {X : Scheme.{u}} (F : X.Modules) (hF : F.IsLocallyFree)
    (x : X) : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  obtain ⟨U, hxU, I, ⟨α⟩⟩ := hF x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  replace hVU : V ≤ U := hVU
  let j : Spec Γ(X, V) ⟶ U := hV.isoSpec.inv ≫ X.homOfLE hVU
  have hj : j ≫ U.ι = hV.fromSpec := by simp [j]; rfl
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let β : F.restrict hV.fromSpec ≅ SheafOfModules.free I :=
    (Scheme.Modules.restrictFunctorCongr hj).symm.app F ≪≫
      (Scheme.Modules.restrictFunctorComp j U.ι).app F ≪≫
      (Scheme.Modules.restrictFunctor j).mapIso α ≪≫ Scheme.Modules.restrictFreeIso j I
  obtain ⟨y, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  rw [free_stalk_restrict_iff hV.fromSpec F y]
  exact free_stalk_free_spec I _ β y

/-- **Hartshorne II, Exercise 5.7(a)**, locally Noetherian form: if `F` is coherent and the
stalk `F_x` is a free `𝒪_{X,x}`-module, then `F` is free on an open neighbourhood of `x`. -/
theorem exists_isFree_restrict_of_free_stalk_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) (hF : IsCoherent F) (x : X)
    (hx : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    ∃ U : X.Opens, x ∈ U ∧ (F.restrict U.ι).IsFree := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let Va : X.affineOpens := ⟨V, hV⟩
  let R := Γ(X, V)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian Va
  obtain ⟨hfin, hiso⟩ := forall_affine_finite_of_isCoherent F hF Va
  let G := specRestriction F Va
  have : Module.Finite R Γ(G, ⊤) := (finite_specRestriction_iff F Va).mpr hfin
  have : Module.FinitePresentation R Γ(G, ⊤) := Module.finitePresentation_of_finite R _
  have hloc : IsLocalizing (modulesSpecToSheaf.obj G) :=
    (isIso_fromTildeΓ_iff_isLocalizing G).mp hiso
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  obtain ⟨y, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have : Module.Free ((Spec R).presheaf.stalk y) (G.presheaf.stalk y) :=
    (free_stalk_restrict_iff hV.fromSpec F y).mp hx
  have := isLocalizedModule_germTopLinear G hloc y
  obtain ⟨r, hr, hfreer, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    y.asIdeal.primeCompl (germTopLinear G y) ((Spec R).presheaf.stalk y)
  let ρ : Γ(G, ⊤) →ₗ[R] Γ(G, CoherentAux.D r) :=
    ((modulesSpecToSheaf.obj G).obj.map (CoherentAux.D r).leTop.op).hom
  have : IsLocalizedModule (Submonoid.powers r) ρ := hloc r
  have : Module.Free Γ(Spec R, CoherentAux.D r) Γ(G, CoherentAux.D r) :=
    free_of_isLocalizedModule_of_free_localization (.powers r) ρ Γ(Spec R, CoherentAux.D r)
  let W : (Spec R).affineOpens := ⟨CoherentAux.D r, by
    have := (isAffineOpen_top (Spec R)).basicOpen ((Scheme.ΓSpecIso R).inv r)
    rwa [basicOpen_eq_of_affine] at this⟩
  have : G.IsQuasicoherent := (isQuasicoherent_iff_isIso_fromTildeΓ G).mpr hiso
  have : (specRestriction G W).IsQuasicoherent := by
    have : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
    exact Scheme.Modules.isQuasicoherent_restrictFunctor W.2.fromSpec G
  have hW : (G.restrict (W : (Spec R).Opens).ι).IsFree := isFree_restrict_of_free_sections G W
  have h2 := isFree_restrict_comp_of_restrict F hV.fromSpec _ hW
  let φ := (W : (Spec R).Opens).ι ≫ hV.fromSpec
  refine ⟨φ.opensRange, ⟨⟨y, hr⟩, rfl⟩, ?_⟩
  exact isFree_restrict_congr F φ.isoOpensRange_inv_comp
    (isFree_restrict_comp F φ φ.isoOpensRange.inv h2)


/-- **Hartshorne II, Exercise 5.7(b)**, locally Noetherian form of the stalkwise criterion: a
coherent sheaf is locally free if and only if all of its stalks are free. -/
theorem isLocallyFree_iff_forall_free_stalk_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) (hF : IsCoherent F) :
    F.IsLocallyFree ↔ ∀ x : X, Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  ⟨free_stalk_of_isLocallyFree F,
    fun h x ↦ exists_isFree_restrict_of_free_stalk_of_isLocallyNoetherian F hF x (h x)⟩

/-- **Hartshorne II, Exercise 5.7(a).** Let `X` be a Noetherian scheme and `F` a coherent
`𝒪_X`-module. If the stalk `F_x` is a free `𝒪_{X,x}`-module, then there is an open
neighbourhood `U` of `x` such that `F|_U` is free. -/
theorem exists_isFree_restrict_of_free_stalk {X : Scheme.{u}} [IsNoetherian X] (F : X.Modules)
    (hF : IsCoherent F) (x : X) (hx : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    ∃ U : X.Opens, x ∈ U ∧ (F.restrict U.ι).IsFree :=
  exists_isFree_restrict_of_free_stalk_of_isLocallyNoetherian F hF x hx

/-- **Hartshorne II, Exercise 5.7(b).** On a Noetherian scheme, a coherent sheaf `F` is locally
free if and only if every stalk `F_x` is a free `𝒪_{X,x}`-module. -/
theorem isLocallyFree_iff_forall_free_stalk {X : Scheme.{u}} [IsNoetherian X] (F : X.Modules)
    (hF : IsCoherent F) :
    F.IsLocallyFree ↔ ∀ x : X, Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  isLocallyFree_iff_forall_free_stalk_of_isLocallyNoetherian F hF

end

end Hartshorne
