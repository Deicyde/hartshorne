/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AffineQuasicoherentAcyclic
import Hartshorne.Cohomology.RightDerivedLongExactSequence
import Hartshorne.Scheme.ModuleIdealSheafData
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.AffineGlobalSectionsExact

/-!
# Serre's criterion for affineness

Hartshorne, *Algebraic Geometry*, III, Theorem 3.7 (pp. 215–216).

For a Noetherian scheme `X` the following are equivalent: `X` is affine; `H^i(X, F) = 0` for all
quasi-coherent `F` and `i > 0`; `H^1(X, J) = 0` for all coherent ideal sheaves `J`
(`Hartshorne.isAffine_tfae_sheafCohomology`).

## Proof

(i) ⇒ (ii) is Theorem III.3.5 (`Hartshorne.sheafCohomology_isZero_of_isQuasicoherent_of_isAffine`)
and (ii) ⇒ (iii) is trivial. For (iii) ⇒ (i) we follow Hartshorne and use the criterion of
Ex. II.2.17 (`AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`).

* *Local step* (`SerreAffineness.exists_affine_basicOpen_of_isClosed`): for a closed point `P`
  with affine neighbourhood `U` and `Y = X ∖ U`, the vanishing of `H^1(X, I_{Y ∪ P})` makes
  `Γ(X, I_Y) ⟶ Γ(X, I_Y / I_{Y ∪ P})` surjective; lifting the section which is `1` near `P` and `0`
  away from `P` gives `f ∈ Γ(X, I_Y)` with `P ∈ X_f ⊆ U`, so `X_f = U_f` is affine.
* *Generation step* (`SerreAffineness.span_eq_top_of_cover`): if `X_{f_1}, …, X_{f_r}` cover `X`,
  then `(f_i) : 𝒪_X^r ⟶ 𝒪_X` is surjective, and its kernel has a filtration whose quotients are
  ideal sheaves (the images of the first coordinate), so `H^1` of the kernel vanishes and `1` lies
  in the image of `Γ(X, 𝒪_X^r)`, i.e. `(f_1, …, f_r) = Γ(X, 𝒪_X)`.
* Every point specializes to a closed point, so the affine `X_f` cover `X`; quasi-compactness and
  the generation step give finitely many generating the unit ideal.

Coherent ideal sheaves are quasi-coherent ideal subsheaves of `𝒪_X`
(`Hartshorne.QuasicoherentIdealSubsheaf`); on a Noetherian scheme they are all coherent
(`SerreAffineness.isCoherent_toModules`). Subobjects of `𝒪_X` given by monomorphisms are turned into
such ideal subsheaves by `SerreAffineness.idealOfMono`.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

namespace SerreAffineness

variable {X : Scheme.{u}}

/-- A short complex of `𝒪_X`-modules, as a short complex in `SheafOfModules`. -/
abbrev toSOM (S : ShortComplex X.Modules) : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
  S

/-- The underlying short complex of abelian sheaves. -/
abbrev Sab (S : ShortComplex X.Modules) : ShortComplex (X.toTopCat.Sheaf AddCommGrpCat.{u}) :=
  (toSOM S).map (ModuleCohomology.toTopSheaf X.ringCatSheaf)

/-- The structure sheaf `𝒪_X` as an `𝒪_X`-module. -/
abbrev unitMod (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- `H^i(X, F)` for an `𝒪_X`-module `F`: cohomology of the underlying abelian sheaf. -/
abbrev H (i : ℕ) (F : X.Modules) : AddCommGrpCat.{u} :=
  (sheafCohomology X.toTopCat i).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)

theorem sab_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) : (Sab S).ShortExact :=
  (show (toSOM S).ShortExact from hS).map_of_exact _

set_option hygiene false in
local notation "Γ₀" => sheafSectionsOver (X := X.toTopCat) ⊤

/-- If `H^1(X, S.X₁) = 0` for a short exact sequence `S` of `𝒪_X`-modules, then
`Γ(X, S.X₂) ⟶ Γ(X, S.X₃)` is surjective. -/
theorem surjective_app_top {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : IsZero (H 1 S.X₁)) : Function.Surjective (S.g.app ⊤) := by
  have hT := sab_shortExact hS
  have hδ : rightDerivedδ Γ₀ hT 0 = 0 := h.eq_of_tgt _ _
  have hepi0 : Epi (((Γ₀).rightDerived 0).map (Sab S).g) :=
    (rightDerived_exact₃ Γ₀ hT 0).epi_f hδ
  have hnat := ((Γ₀).rightDerivedZeroIsoSelf).hom.naturality (Sab S).g
  have e : (Γ₀).map (Sab S).g = ((Γ₀).rightDerivedZeroIsoSelf).inv.app (Sab S).X₂ ≫
      ((Γ₀).rightDerived 0).map (Sab S).g ≫ ((Γ₀).rightDerivedZeroIsoSelf).hom.app (Sab S).X₃ := by
    rw [hnat, Iso.inv_hom_id_app_assoc]
  have hepi : Epi ((Γ₀).map (Sab S).g) := by rw [e]; infer_instance
  exact (AddCommGrpCat.epi_iff_surjective _).1 hepi

/-- `H^1` vanishes on the middle term of a short exact sequence whose outer terms have
vanishing `H^1`. -/
theorem isZero_H1_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : IsZero (H 1 S.X₁)) (h₃ : IsZero (H 1 S.X₃)) : IsZero (H 1 S.X₂) :=
  (rightDerived_exact₂ Γ₀ (sab_shortExact hS) 1).isZero_of_both_zeros (h₁.eq_of_src _ _)
    (h₃.eq_of_tgt _ _)

/-! ### Ideal sheaves from monomorphisms into `𝒪_X` -/

section IdealOfMono

open ArtinReesKernelSheaf

variable {M : X.Modules} (ι : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) [Mono ι]

/-- The image of a monomorphism `M ⟶ 𝒪_X`, as a family of ideals. -/
def rangeSubmodule : (SheafOfModules.unit X.ringCatSheaf : X.Modules).val.Submodule where
  obj U := LinearMap.range (ι.val.app U).hom
  map i := by
    rintro _ ⟨s, rfl⟩
    exact ⟨M.val.map i s, PresheafOfModules.naturality_apply _ _ _⟩

/-- `M` corestricted to the image of `ι`. -/
def toRange : M.val ⟶ (rangeSubmodule ι).toPresheafOfModules :=
  PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun s := ⟨ι.val.app U s, s, rfl⟩
          map_zero' := Subtype.ext (ι.val.app U).hom.map_zero
          map_add' a b := Subtype.ext ((ι.val.app U).hom.map_add a b) }
      naturality U V i := by
        ext s
        exact Subtype.ext (PresheafOfModules.naturality_apply ι.val i s) }
    fun U r m => Subtype.ext ((ι.val.app U).hom.map_smul r m)

theorem isIso_toRange : IsIso (toRange ι) := by
  have : Mono (toRange ι) := PresheafOfModules.mono_of_injective fun U a b h =>
    modules_app_injective ι U.unop (congrArg Subtype.val h)
  have : Epi (toRange ι) := PresheafOfModules.epi_of_surjective fun U t => by
    obtain ⟨_, s, rfl⟩ := t
    exact ⟨s, rfl⟩
  exact isIso_of_mono_of_epi _

theorem isLocal_rangeSubmodule : IsLocal (rangeSubmodule ι) :=
  isLocal_of_isSheaf _ ((Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf _).mapIso (@asIso _ _ _ _ (toRange ι) (isIso_toRange ι)))).1
      M.isSheaf)

/-- `M` is isomorphic to the image of `ι`. -/
def rangeIso : M ≅ toModules (rangeSubmodule ι) (isLocal_rangeSubmodule ι) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (@asIso _ _ _ _ (toRange ι) (isIso_toRange ι))

/-- The quasi-coherent ideal subsheaf of `𝒪_X` given by a monomorphism from a quasi-coherent
module. -/
def idealOfMono [M.IsQuasicoherent] : QuasicoherentIdealSubsheaf X where
  carrier := rangeSubmodule ι
  isLocal := isLocal_rangeSubmodule ι
  isQuasicoherent := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (rangeIso ι)
    inferInstance

/-- `M` is isomorphic to the module of its ideal subsheaf. -/
def idealOfMonoIso [M.IsQuasicoherent] : M ≅ (idealOfMono ι).toModules := rangeIso ι

end IdealOfMono

/-- On a locally Noetherian scheme every quasi-coherent ideal subsheaf of `𝒪_X` is coherent. -/
theorem isCoherent_toModules [IsLocallyNoetherian X] (J : QuasicoherentIdealSubsheaf X) :
    IsCoherent J.toModules := by
  have := J.isQuasicoherent
  have hiso := ((quasicoherent_affine_local_tfae J.toModules).out 0 2).mp J.isQuasicoherent
  refine ((coherent_affine_local_tfae J.toModules).out 3 0).mp ?_
  intro U
  refine ⟨?_, hiso U⟩
  have : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherian Γ(X, (U : X.Opens)) Γ(unitMod X, (U : X.Opens)) :=
    inferInstanceAs (IsNoetherian Γ(X, (U : X.Opens)) Γ(X, (U : X.Opens)))
  change Module.Finite Γ(X, (U : X.Opens)) (ArtinReesKernelSheaf.sub J.carrier (U : X.Opens))
  infer_instance

/-! ### The finite generation step -/

section Generation

/-- Multiplication by a global section of `𝒪_X`, as an endomorphism of an `𝒪_X`-module. -/
def smulHom (f : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (M.val.obj U)
        (X.ringCatSheaf.obj.map (homOfLE le_top : U.unop ⟶ ⊤).op f))
      naturality U V i := by
        ext x
        change X.ringCatSheaf.obj.map (homOfLE le_top : V.unop ⟶ ⊤).op f • M.val.map i x =
          M.val.map i (X.ringCatSheaf.obj.map (homOfLE le_top : U.unop ⟶ ⊤).op f •
            (x : M.val.obj U))
        have h := M.val.map_smul i (X.ringCatSheaf.obj.map (homOfLE le_top : U.unop ⟶ ⊤).op f)
          (x : M.val.obj U)
        refine Eq.trans ?_ h.symm
        have hr : X.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op f =
            X.presheaf.map i (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op f) := by
          rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
          rfl
        exact congrArg (fun r => r • M.val.map i x) hr }
    fun U r m => by
      change X.ringCatSheaf.obj.map (homOfLE le_top : U.unop ⟶ ⊤).op f • r • m =
        r • X.ringCatSheaf.obj.map (homOfLE le_top : U.unop ⟶ ⊤).op f • m
      rw [smul_smul, smul_smul]
      congr 1
      exact mul_comm (G := X.presheaf.obj U) _ _⟩

theorem smulHom_app (f : Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    (smulHom f M).app U x = X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op f • x :=
  rfl

open ZeroObject in
/-- The free module `𝒪_X^{l}` on a list of global sections. -/
noncomputable def freeL : List Γ(X, ⊤) → X.Modules
  | [] => 0
  | _ :: l => unitMod X ⊞ freeL l

/-- The map `𝒪_X^{l} ⟶ 𝒪_X`, `(a_f) ↦ Σ f a_f`. -/
noncomputable def αL : (l : List Γ(X, ⊤)) → (freeL l ⟶ unitMod X)
  | [] => 0
  | f :: l => biprod.desc (smulHom f (unitMod X)) (αL l)

/-- A section of `𝒪_X`, viewed as an `𝒪_X`-module, as a section of the structure sheaf. -/
abbrev toRing {U : X.Opens} (x : Γ(unitMod X, U)) : Γ(X, U) := x

/-- A section of the structure sheaf, as a section of `𝒪_X` viewed as an `𝒪_X`-module. -/
abbrev ofRing {U : X.Opens} (r : Γ(X, U)) : Γ(unitMod X, U) := r

theorem res_ofRing {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) :
    ArtinReesKernelSheaf.res (unitMod X) h (ofRing r) = ofRing (X.presheaf.map (homOfLE h).op r) :=
  rfl

theorem restrict_top_self (f : Γ(X, ⊤)) :
    X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op f = f := by
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

theorem biprod_app_eq {A B : X.Modules} {U : X.Opens} (z : Γ(A ⊞ B, U)) :
    z = (biprod.fst ≫ biprod.inl : A ⊞ B ⟶ _).app U z +
      (biprod.snd ≫ biprod.inr : A ⊞ B ⟶ _).app U z := by
  have h := congrArg (fun φ : A ⊞ B ⟶ A ⊞ B => φ.app U z) biprod.total
  simp only [Scheme.Modules.Hom.add_app, AddCommGrpCat.hom_add_apply] at h
  exact h.symm

/-- The global sections in the image of `αL l` lie in the ideal generated by `l`. -/
theorem αL_app_top_mem : ∀ (l : List Γ(X, ⊤)) (z : Γ(freeL l, ⊤)),
    toRing ((αL l).app ⊤ z) ∈ Ideal.span {g | g ∈ l}
  | [], z => by
    change toRing ((0 : freeL [] ⟶ unitMod X).app ⊤ z) ∈ _
    rw [Scheme.Modules.Hom.zero_app]
    exact Ideal.zero_mem _
  | f :: l, z => by
    revert z
    change ∀ z : Γ(unitMod X ⊞ freeL l, ⊤), toRing ((biprod.desc (smulHom f (unitMod X))
      (αL l) : unitMod X ⊞ freeL l ⟶ _).app ⊤ z) ∈ Ideal.span {g | g ∈ f :: l}
    intro z
    rw [biprod_app_eq z, map_add]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Category.assoc]
      rw [biprod.inl_desc, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, smulHom_app,
        restrict_top_self]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (List.mem_cons_self))
    · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Category.assoc]
      rw [biprod.inr_desc, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
      exact Ideal.span_mono (fun g hg => List.mem_cons_of_mem f hg) (αL_app_top_mem l _)

/-- `αL l` is locally surjective at the points of `⋃_{f ∈ l} X_f`. -/
theorem αL_locally_surjective : ∀ (l : List Γ(X, ⊤)) {V : X.Opens} (t : Γ(unitMod X, V)) {x : X},
    x ∈ V → (∃ f ∈ l, x ∈ X.basicOpen f) → ∃ (W : X.Opens) (hWV : W ≤ V), x ∈ W ∧
      ∃ z : Γ(freeL l, W), (αL l).app W z = (unitMod X).presheaf.map (homOfLE hWV).op t
  | [], _, _, _, _, ⟨_, hg, _⟩ => absurd hg List.not_mem_nil
  | f :: l, V, t, x, hx, ⟨g, hg, hxg⟩ => by
    by_cases hxf : x ∈ X.basicOpen f
    · let W : X.Opens := V ⊓ X.basicOpen f
      have hWV : W ≤ V := inf_le_left
      have hWf : W ≤ X.basicOpen f := inf_le_right
      let u : Γ(X, W) := X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op f
      have hu : IsUnit u := by
        have h1 := X.toRingedSpace.isUnit_res_basicOpen f
        have h2 := h1.map (X.presheaf.map (homOfLE hWf).op).hom
        have : u = (X.presheaf.map (homOfLE hWf).op).hom
            ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op) f) := by
          change _ = (X.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫
            X.presheaf.map (homOfLE hWf).op) f
          rw [← X.presheaf.map_comp]
          rfl
        rw [this]
        exact h2
      refine ⟨W, hWV, ⟨hx, hxf⟩, ?_⟩
      let t' : Γ(unitMod X, W) := (unitMod X).presheaf.map (homOfLE hWV).op t
      refine ⟨(biprod.inl : unitMod X ⟶ unitMod X ⊞ freeL l).app W ((hu.unit⁻¹ : Γ(X, W)ˣ) • t'),
        ?_⟩
      change (biprod.inl ≫ biprod.desc (smulHom f (unitMod X)) (αL l)).app W _ = t'
      rw [biprod.inl_desc, smulHom_app]
      change u • ((hu.unit⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) • t' = t'
      rw [smul_smul, IsUnit.mul_val_inv, one_smul]
    · have hgl : g ∈ l := by
        rcases List.mem_cons.mp hg with rfl | h
        · exact absurd hxg hxf
        · exact h
      obtain ⟨W, hWV, hxW, z, hz⟩ := αL_locally_surjective l t hx ⟨g, hgl, hxg⟩
      refine ⟨W, hWV, hxW, (biprod.inr : freeL l ⟶ unitMod X ⊞ freeL l).app W z, ?_⟩
      change (biprod.inr ≫ biprod.desc (smulHom f (unitMod X)) (αL l)).app W z = _
      rw [biprod.inr_desc]
      exact hz

theorem epi_αL (l : List Γ(X, ⊤)) (hl : ∀ x : X, ∃ f ∈ l, x ∈ X.basicOpen f) : Epi (αL l) := by
  have : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map (αL l)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).1
      ((TopCat.Presheaf.isLocallySurjective_iff _).2 fun V t x hx => by
        obtain ⟨W, hWV, hxW, z, hz⟩ := αL_locally_surjective l t hx (hl x)
        exact ⟨W, hWV, ⟨z, hz⟩, hxW⟩)
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map this

instance isQuasicoherent_unitMod (X : Scheme.{u}) : (unitMod X).IsQuasicoherent :=
  ClosedImmersionIdeal.isQuasicoherent_unit X

open ZeroObject in
theorem isQuasicoherent_freeL : ∀ l : List Γ(X, ⊤), (freeL l).IsQuasicoherent
  | [] => by
    have : (kernel (𝟙 (unitMod X))).IsQuasicoherent := isQuasicoherent_kernel _
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((isZero_kernel_of_mono (𝟙 (unitMod X))).iso (isZero_zero _)) this
  | _ :: l => by
    have := isQuasicoherent_freeL l
    exact isQuasicoherent_of_shortExact (S := ShortComplex.mk
      (biprod.inl : unitMod X ⟶ unitMod X ⊞ freeL l) biprod.snd biprod.inl_snd)
      (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact

theorem isZero_H_of_isZero {F : X.Modules} (hF : IsZero F) (i : ℕ) : IsZero (H i F) :=
  (sheafCohomology X.toTopCat i).map_isZero ((SheafOfModules.toSheaf X.ringCatSheaf).map_isZero hF)

/-- `𝒪_X^{f :: l} = 𝒪_X ⊞ 𝒪_X^{l}`. -/
def consIso (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) : freeL (f :: l) ≅ unitMod X ⊞ freeL l := Iso.refl _

theorem αL_cons (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) :
    αL (f :: l) = (consIso f l).hom ≫ biprod.desc (smulHom f (unitMod X)) (αL l) := rfl

@[reassoc]
theorem inr_inv_αL (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) :
    (biprod.inr : freeL l ⟶ unitMod X ⊞ freeL l) ≫ (consIso f l).inv ≫ αL (f :: l) = αL l := by
  rw [αL_cons, Iso.inv_hom_id_assoc, biprod.inr_desc]

/-- The inclusion `ker(αL l) ⟶ ker(αL (f :: l))` through the second summand. -/
def kerIncl (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) : kernel (αL l) ⟶ kernel (αL (f :: l)) :=
  kernel.lift (αL (f :: l)) (kernel.ι (αL l) ≫ biprod.inr ≫ (consIso f l).inv) (by
    rw [αL_cons, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_desc,
      kernel.condition])

/-- The first coordinate `ker(αL (f :: l)) ⟶ 𝒪_X`. -/
def kerFst (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) : kernel (αL (f :: l)) ⟶ unitMod X :=
  kernel.ι (αL (f :: l)) ≫ (consIso f l).hom ≫ biprod.fst

@[reassoc (attr := simp)]
theorem kerIncl_ι (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) :
    kerIncl f l ≫ kernel.ι (αL (f :: l)) = kernel.ι (αL l) ≫ biprod.inr ≫ (consIso f l).inv :=
  kernel.lift_ι _ _ _

instance (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) : Mono (kerIncl f l) := by
  have : Mono (kerIncl f l ≫ kernel.ι (αL (f :: l))) := by
    rw [kerIncl_ι]
    infer_instance
  exact mono_of_mono _ (kernel.ι (αL (f :: l)))

theorem kerIncl_kerFst (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) : kerIncl f l ≫ kerFst f l = 0 := by
  rw [kerFst, kerIncl_ι_assoc, Iso.inv_hom_id_assoc, biprod.inr_fst, comp_zero]

/-- The short exact sequence `0 ⟶ ker(αL l) ⟶ ker(αL (f :: l)) ⟶ J ⟶ 0`, with `J ⊆ 𝒪_X` the
image of the first coordinate. -/
abbrev kerSC (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) : ShortComplex X.Modules :=
  ShortComplex.mk (kerIncl f l) (factorThruImage (kerFst f l)) (by
    rw [← cancel_mono (image.ι (kerFst f l)), Category.assoc, image.fac, kerIncl_kerFst,
      zero_comp])

theorem kerSC_shortExact (f : Γ(X, ⊤)) (l : List Γ(X, ⊤)) : (kerSC f l).ShortExact := by
  have : Mono (kerSC f l).f := inferInstanceAs (Mono (kerIncl f l))
  have : Epi (kerSC f l).g := inferInstanceAs (Epi (factorThruImage (kerFst f l)))
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_) inferInstance
    inferInstance
  have key : ∀ {T : X.Modules} (k : T ⟶ kernel (αL (f :: l))), k ≫ kerFst f l = 0 →
      k ≫ kernel.ι (αL (f :: l)) = (k ≫ kernel.ι (αL (f :: l)) ≫ (consIso f l).hom ≫
        biprod.snd) ≫ biprod.inr ≫ (consIso f l).inv := fun {T} k hk => by
    rw [← cancel_mono (consIso f l).hom]
    apply biprod.hom_ext
    · simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_fst, comp_zero]
      exact hk
    · simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd, Category.comp_id]
  have hfac : ∀ {T : X.Modules} (k : T ⟶ kernel (αL (f :: l))), k ≫ (kerSC f l).g = 0 →
      k ≫ kerFst f l = 0 := fun {T} k hk => by
    rw [← image.fac (kerFst f l), ← Category.assoc]
    change k ≫ factorThruImage (kerFst f l) = 0 at hk
    rw [hk, zero_comp]
  refine KernelFork.IsLimit.ofι _ _ (fun {T} k hk => kernel.lift (αL l)
      (k ≫ kernel.ι (αL (f :: l)) ≫ (consIso f l).hom ≫ biprod.snd) ?_) ?_ ?_
  · have h1 := key k (hfac k hk)
    have h2 : (k ≫ kernel.ι (αL (f :: l))) ≫ αL (f :: l) = 0 := by
      rw [Category.assoc, kernel.condition, comp_zero]
    rw [h1] at h2
    simpa only [Category.assoc, inr_inv_αL] using h2
  · intro T k hk
    rw [← cancel_mono (kernel.ι (αL (f :: l)))]
    change (kernel.lift _ _ _ ≫ kerIncl f l) ≫ kernel.ι (αL (f :: l)) = _
    rw [Category.assoc, kerIncl_ι, kernel.lift_ι_assoc, key k (hfac k hk)]
  · intro T k hk m hm
    rw [← cancel_mono (kernel.ι (αL l)), kernel.lift_ι]
    change m ≫ kerIncl f l = k at hm
    rw [← hm]
    simp only [Category.assoc, kerIncl_ι_assoc, Iso.inv_hom_id_assoc, biprod.inr_snd,
      Category.comp_id]

open ZeroObject in
/-- If `H^1` vanishes on all quasi-coherent ideal sheaves, it vanishes on `ker(𝒪_X^{l} ⟶ 𝒪_X)`,
by induction on `l` using the filtration by the coordinate ideal sheaves. -/
theorem isZero_H1_ker (hIII : ∀ J : QuasicoherentIdealSubsheaf X, IsZero (H 1 J.toModules)) :
    ∀ l : List Γ(X, ⊤), IsZero (H 1 (kernel (αL l)))
  | [] => isZero_H_of_isZero
      (IsZero.of_mono (kernel.ι (αL [])) (show IsZero (freeL ([] : List Γ(X, ⊤))) from
        isZero_zero _)) 1
  | f :: l => by
    have hK := isZero_H1_ker hIII l
    have := isQuasicoherent_freeL (f :: l)
    have : (kernel (αL (f :: l))).IsQuasicoherent := isQuasicoherent_kernel _
    have : (image (kerFst f l)).IsQuasicoherent := isQuasicoherent_image _
    have : Mono (image.ι (kerFst f l)) := inferInstance
    have hJ : IsZero (H 1 (image (kerFst f l))) :=
      (hIII (idealOfMono (image.ι (kerFst f l)))).of_iso
        ((sheafCohomology X.toTopCat 1).mapIso ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso
          (idealOfMonoIso (image.ι (kerFst f l)))))
    exact isZero_H1_of_shortExact (kerSC_shortExact f l) hK hJ

/-- **Generation step** (Hartshorne III.3.7): if `H^1` vanishes on all quasi-coherent ideal
sheaves and the `X_f`, `f ∈ l`, cover `X`, then the `f ∈ l` generate the unit ideal of
`Γ(X, 𝒪_X)`. -/
theorem span_eq_top_of_cover (hIII : ∀ J : QuasicoherentIdealSubsheaf X, IsZero (H 1 J.toModules))
    (l : List Γ(X, ⊤)) (hl : ∀ x : X, ∃ f ∈ l, x ∈ X.basicOpen f) :
    Ideal.span {g | g ∈ l} = ⊤ := by
  have := epi_αL l hl
  let S := ShortComplex.mk (kernel.ι (αL l)) (αL l) (kernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel (kernelIsKernel _)) inferInstance
      inferInstance
  obtain ⟨z, hz⟩ := surjective_app_top hS (isZero_H1_ker hIII l)
    (show Γ(unitMod X, ⊤) from (1 : Γ(X, ⊤)))
  have h := αL_app_top_mem l z
  change toRing (S.g.app ⊤ z) ∈ _ at h
  rw [hz] at h
  exact (Ideal.eq_top_iff_one _).2 h

end Generation

/-! ### The local step -/

section Local

open ArtinReesKernelSheaf

/-- A section over an affine open vanishes at the point of a prime ideal exactly when it lies in
that prime. -/
theorem fromSpec_mem_basicOpen_iff {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (p : PrimeSpectrum Γ(X, U)) : hU.fromSpec p ∈ X.basicOpen f ↔ f ∉ p.asIdeal := by
  have h := congrArg (fun W : (Spec Γ(X, U)).Opens => p ∈ W) (hU.fromSpec_preimage_basicOpen f)
  exact h.to_iff

/-- A section of the vanishing ideal of `Z` over an affine open `V` vanishes at every point of
`Z ∩ V`. -/
theorem not_mem_basicOpen_of_mem_vanishingIdeal {Z : Closeds X} {V : X.affineOpens}
    {f : Γ(X, (V : X.Opens))} (hf : f ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal V)
    {x : X} (hxV : x ∈ (V : X.Opens)) (hxZ : x ∈ Z) : x ∉ X.basicOpen f := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal] at hf
  obtain ⟨p, rfl⟩ : x ∈ Set.range V.2.fromSpec := by rwa [V.2.range_fromSpec]
  exact fun h => (fromSpec_mem_basicOpen_iff V.2 f p).1 h (hf p hxZ)

/-- The vanishing ideal of `Z` is the unit ideal over an affine open disjoint from `Z`. -/
theorem one_mem_vanishingIdeal {Z : Closeds X} {V : X.affineOpens}
    (hV : ∀ x ∈ (V : X.Opens), x ∉ Z) :
    (1 : Γ(X, (V : X.Opens))) ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal V := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro p hp
  have hmem : V.2.fromSpec p ∈ (V : X.Opens) :=
    (Set.ext_iff.mp (IsAffineOpen.range_fromSpec (U := (V : X.Opens)) V.2) _).mp
      (Set.mem_range_self p)
  exact absurd hp (hV _ hmem)

/-- The ideal sheaf `I_Z` of a closed subset (of its reduced induced structure). -/
def vI (Z : Closeds X) : QuasicoherentIdealSubsheaf X :=
  idealSheafDataToSubsheaf (Scheme.IdealSheafData.vanishingIdeal Z)

theorem mem_vI_iff (Z : Closeds X) (V : X.affineOpens) (s : Γ(unitMod X, (V : X.Opens))) :
    s ∈ sub (vI Z).carrier V ↔
      toRing s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal V := by
  change toRing s ∈ (vI Z).ideal V ↔ _
  rw [vI, ideal_idealSheafDataToSubsheaf]

/-- A section lies in `I_Z` if it lies in the vanishing ideal of `Z` on affine opens covering its
domain. -/
theorem mem_vI_of_local (Z : Closeds X) {W : X.Opens} (s : Γ(unitMod X, W))
    (h : ∀ V : X.affineOpens, (V : X.Opens) ≤ W →
      ∀ hVW : (V : X.Opens) ≤ W, toRing (res (unitMod X) hVW s) ∈
        (Scheme.IdealSheafData.vanishingIdeal Z).ideal V) :
    s ∈ sub (vI Z).carrier W := by
  refine (vI Z).isLocal W s fun x hx => ?_
  obtain ⟨V, hVW, hxV⟩ := exists_affine_le hx
  exact ⟨V, hVW, hxV, (mem_vI_iff Z V _).2 (h V hVW hVW)⟩

theorem vI_le {Y Z : Closeds X} (h : Y ≤ Z) : (vI Z).carrier ≤ (vI Y).carrier := by
  rw [PresheafOfModules.Submodule.le_iff]
  intro W s hs
  refine mem_vI_of_local Y s fun V _ hVW => ?_
  have h1 := res_mem (vI Z).carrier hVW hs
  rw [mem_vI_iff] at h1
  exact (Scheme.IdealSheafData.le_def.mp (Scheme.IdealSheafData.vanishingIdeal_antimono h) V) h1

/-- The inclusion `I_Z ⟶ I_Y` for `Y ⊆ Z`. -/
def vIIncl {Y Z : Closeds X} (h : Y ≤ Z) : (vI Z).toModules ⟶ (vI Y).toModules :=
  inclusion (vI Z).isLocal (vI Y).isLocal (vI_le h)

theorem inclusion_app_val {E : X.Modules} {N₁ N₂ : E.val.Submodule} (h₁ : IsLocal N₁)
    (h₂ : IsLocal N₂) (h : N₁ ≤ N₂) (V : X.Opens) (g : Γ(toModules N₁ h₁, V)) :
    ((inclusion h₁ h₂ h).app V g).1 = g.1 :=
  rfl

theorem vIIncl_app_val {Y Z : Closeds X} (h : Y ≤ Z) (V : X.Opens)
    (g : Γ((vI Z).toModules, V)) : ((vIIncl h).app V g).1 = g.1 :=
  inclusion_app_val _ _ _ V g

instance {Y Z : Closeds X} (h : Y ≤ Z) : Mono (vIIncl h) := by
  have : Mono ((SheafOfModules.forget X.ringCatSheaf).map (vIIncl h)) :=
    inferInstanceAs (Mono (PresheafOfModules.Submodule.homOfLE (vI_le h)))
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map this

/-- **Local step** (Hartshorne III.3.7): if `H^1` vanishes on all quasi-coherent ideal sheaves,
every closed point `P` has an affine neighbourhood of the form `X_f`. Take an affine open
`U ∋ P`, `Y = X ∖ U`, and the ideal sheaves `I_{Y ∪ P} ⊆ I_Y`; since `H^1(X, I_{Y ∪ P}) = 0`, the
section of `I_Y / I_{Y ∪ P}` equal to `1` near `P` and `0` away from `P` lifts to
`f ∈ Γ(X, I_Y)`; then `P ∈ X_f ⊆ U`, so `X_f = U_f` is affine. -/
theorem exists_affine_basicOpen_of_isClosed
    (hIII : ∀ J : QuasicoherentIdealSubsheaf X, IsZero (H 1 J.toModules)) (P : X)
    (hP : IsClosed ({P} : Set X)) :
    ∃ f : Γ(X, ⊤), P ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by
  obtain ⟨U, -, hPU⟩ := exists_affine_le (show P ∈ (⊤ : X.Opens) from trivial)
  let Y : Closeds X := ⟨((U : X.Opens) : Set X)ᶜ, (U : X.Opens).isOpen.isClosed_compl⟩
  let Z : Closeds X := Y ⊔ ⟨{P}, hP⟩
  have hYZ : Y ≤ Z := le_sup_left
  have hPZ : P ∈ Z := Or.inr rfl
  let ι := vIIncl hYZ
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel _)) inferInstance
      inferInstance
  have hsurj := surjective_app_top hS (hIII (vI Z))
  let Pc : X.Opens := ⟨({P} : Set X)ᶜ, hP.isOpen_compl⟩
  -- the section `1` of `I_Y` over `U`
  have h1U : ofRing (1 : Γ(X, (U : X.Opens))) ∈ sub (vI Y).carrier (U : X.Opens) :=
    (mem_vI_iff Y U _).2 (one_mem_vanishingIdeal fun x hx hxY => hxY hx)
  let oneU : Γ((vI Y).toModules, (U : X.Opens)) := ⟨ofRing 1, h1U⟩
  -- away from `P`, the section `1` of `𝒪_X` over a part of `U` lies in `I_Z`
  have h1V : ∀ (V : X.Opens), V ≤ (U : X.Opens) → V ≤ Pc →
      ofRing (1 : Γ(X, V)) ∈ sub (vI Z).carrier V := by
    intro V hVU hVP
    refine mem_vI_of_local Z _ fun V' hV' hV'' => ?_
    rw [res_ofRing, map_one]
    refine one_mem_vanishingIdeal fun x hx hxZ => ?_
    rcases hxZ with hxY | hxP
    · exact hxY (hVU (hV' hx))
    · exact hVP (hV' hx) hxP
  let Q := cokernel ι
  have hres : ∀ (V : X.Opens) (hVU : V ≤ (U : X.Opens)), V ≤ Pc →
      Q.presheaf.map (homOfLE hVU).op ((cokernel.π ι).app (U : X.Opens) oneU) = 0 := by
    intro V hVU hVP
    have hnat := ConcreteCategory.congr_hom ((cokernel.π ι).mapPresheaf.naturality
      (homOfLE hVU).op) oneU
    simp only [Scheme.Modules.mapPresheaf_app] at hnat
    change ((vI Y).toModules.presheaf.map (homOfLE hVU).op ≫
      (cokernel.π ι).app V) oneU = _ at hnat
    rw [← ConcreteCategory.comp_apply, ← hnat]
    have hel : (vI Y).toModules.presheaf.map (homOfLE hVU).op oneU =
        ι.app V ⟨ofRing 1, h1V V hVU hVP⟩ := by
      apply Subtype.ext
      exact map_one (X.presheaf.map (homOfLE hVU).op).hom
    rw [ConcreteCategory.comp_apply, hel]
    exact (ConcreteCategory.congr_hom (congrArg (fun φ => φ.app V)
      (cokernel.condition ι)) _).trans rfl
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf X.ringCatSheaf).obj Q
  let W : Bool → X.Opens := fun b => cond b (U : X.Opens) Pc
  let sf : ∀ b : Bool, ToType (F.1.obj (op (W b))) := fun b => match b with
    | true => (cokernel.π ι).app (U : X.Opens) oneU
    | false => 0
  have hcompat : TopCat.Presheaf.IsCompatible F.1 W sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (map_zero _).trans (hres _ _ inf_le_left).symm
    · exact (hres _ _ inf_le_right).trans (map_zero _).symm
    · rfl
  have hcover : (⊤ : X.Opens) ≤ iSup W := by
    intro x _
    refine Opens.mem_iSup.mpr ?_
    by_cases hx : x = P
    · exact ⟨true, hx ▸ hPU⟩
    · exact ⟨false, hx⟩
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' W ⊤ (fun b => homOfLE le_top) hcover sf hcompat
  obtain ⟨f₀, hf₀⟩ := hsurj t
  let f : Γ(X, ⊤) := toRing (f₀ : Γ((vI Y).toModules, ⊤)).1
  -- `P ∈ X_f`
  have hPf : P ∈ X.basicOpen f := by
    let r : Γ((vI Y).toModules, (U : X.Opens)) :=
      (vI Y).toModules.presheaf.map (homOfLE le_top : (U : X.Opens) ⟶ ⊤).op f₀ - oneU
    have hr : (cokernel.π ι).app (U : X.Opens) r = 0 := by
      have hnat := ConcreteCategory.congr_hom ((cokernel.π ι).mapPresheaf.naturality
        (homOfLE le_top : (U : X.Opens) ⟶ ⊤).op) f₀
      simp only [Scheme.Modules.mapPresheaf_app] at hnat
      rw [map_sub, sub_eq_zero]
      refine hnat.trans ?_
      rw [ConcreteCategory.comp_apply]
      change F.1.map _ ((cokernel.π ι).app ⊤ f₀) = _
      rw [show (cokernel.π ι).app ⊤ f₀ = t from hf₀]
      exact ht true
    have : Mono S.f := inferInstanceAs (Mono ι)
    obtain ⟨g, hg⟩ := modules_sections_exact hS.exact (U := (U : X.Opens)) r hr
    have hmem : (r : Γ((vI Y).toModules, (U : X.Opens))).1 ∈ sub (vI Z).carrier (U : X.Opens) := by
      rw [← hg]
      change ((vIIncl hYZ).app (U : X.Opens) g).1 ∈ _
      rw [vIIncl_app_val]
      exact g.2
    have hnot := not_mem_basicOpen_of_mem_vanishingIdeal ((mem_vI_iff Z U _).1 hmem) hPU hPZ
    obtain ⟨p, hp⟩ : P ∈ Set.range U.2.fromSpec := by rwa [U.2.range_fromSpec]
    by_contra hPf'
    have h1 : X.presheaf.map (homOfLE le_top : (U : X.Opens) ⟶ ⊤).op f ∈ p.asIdeal := by
      by_contra hc
      have h := (fromSpec_mem_basicOpen_iff U.2 _ p).2 hc
      rw [hp, Scheme.basicOpen_res] at h
      exact hPf' h.2
    have h2 : toRing r.1 ∈ p.asIdeal := by
      by_contra hc
      have h := (fromSpec_mem_basicOpen_iff U.2 _ p).2 hc
      rw [hp] at h
      exact hnot h
    have h3 : toRing r.1 = X.presheaf.map (homOfLE le_top : (U : X.Opens) ⟶ ⊤).op f - 1 := rfl
    rw [h3] at h2
    have h4 := p.asIdeal.sub_mem h1 h2
    rw [sub_sub_cancel] at h4
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h4)
  -- `X_f ⊆ U`
  have hfU : X.basicOpen f ≤ (U : X.Opens) := by
    intro x hxf
    by_contra hxU
    obtain ⟨V, -, hxV⟩ := exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
    have hmem := res_mem (vI Y).carrier (le_top : (V : X.Opens) ≤ ⊤)
      (f₀ : Γ((vI Y).toModules, ⊤)).2
    have hnot := not_mem_basicOpen_of_mem_vanishingIdeal ((mem_vI_iff Y V _).1 hmem) hxV hxU
    change x ∉ X.basicOpen (X.presheaf.map (homOfLE le_top : (V : X.Opens) ⟶ ⊤).op f) at hnot
    rw [Scheme.basicOpen_res] at hnot
    exact hnot ⟨hxV, hxf⟩
  refine ⟨f, hPf, ?_⟩
  have hb : X.basicOpen (X.presheaf.map (homOfLE le_top : (U : X.Opens) ⟶ ⊤).op f) =
      X.basicOpen f := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 hfU
  rw [← hb]
  exact U.2.basicOpen _

end Local

/-- **Combination step** (Hartshorne III.3.7, end of the proof, via Ex. II.2.17): if every closed
point of a Noetherian scheme has an affine neighbourhood `X_f`, and every finite family `f_i`
with `⋃ X_{f_i} = X` generates the unit ideal of `Γ(X, 𝒪_X)`, then `X` is affine. -/
theorem isAffine_of_local_of_generation [IsNoetherian X]
    (hA : ∀ P : X, IsClosed ({P} : Set X) →
      ∃ f : Γ(X, ⊤), P ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f))
    (hB : ∀ t : Finset Γ(X, ⊤), (∀ x : X, ∃ f ∈ t, x ∈ X.basicOpen f) →
      Ideal.span (t : Set Γ(X, ⊤)) = ⊤) :
    IsAffine X := by
  let S : Set Γ(X, ⊤) := {f | IsAffineOpen (X.basicOpen f)}
  have hcover : (Set.univ : Set X) ⊆ ⋃ f : S, (X.basicOpen f.1 : Set X) := by
    intro x _
    obtain ⟨P, hP, hPc⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
      ⟨x, subset_closure rfl⟩
    obtain ⟨f, hPf, hf⟩ := hA P hPc
    have hxP : x ⤳ P := specializes_iff_mem_closure.mpr hP
    exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxP.mem_open (X.basicOpen f).isOpen hPf⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun f : S => (X.basicOpen f.1).isOpen)
    hcover
  classical
  let t' : Finset Γ(X, ⊤) := t.image Subtype.val
  have hspan : Ideal.span (t' : Set Γ(X, ⊤)) = ⊤ := by
    refine hB t' fun x => ?_
    obtain ⟨f, hft, hxf⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨f.1, Finset.mem_image_of_mem _ hft, hxf⟩
  refine isAffine_of_isAffineOpen_basicOpen (t' : Set Γ(X, ⊤)) hspan fun f hf => ?_
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hf
  exact g.2

/-- **(iii) ⇒ (i)** of Hartshorne III, Theorem 3.7: a Noetherian scheme on which `H^1` vanishes
for every quasi-coherent ideal sheaf is affine. -/
theorem isAffine_of_isZero_H1 [IsNoetherian X]
    (hIII : ∀ J : QuasicoherentIdealSubsheaf X, IsZero (H 1 J.toModules)) : IsAffine X := by
  refine isAffine_of_local_of_generation (fun P hP => exists_affine_basicOpen_of_isClosed hIII P hP)
    fun t ht => ?_
  have h := span_eq_top_of_cover hIII t.toList fun x => by
    obtain ⟨f, hf, hx⟩ := ht x
    exact ⟨f, Finset.mem_toList.2 hf, hx⟩
  have he : {g | g ∈ t.toList} = (t : Set Γ(X, ⊤)) := by
    ext g
    simp
  rwa [he] at h

end SerreAffineness

open SerreAffineness in
/-- **Serre's criterion for affineness** (Hartshorne III, Theorem 3.7). For a Noetherian scheme
`X` the following are equivalent:
1. `X` is affine;
2. `H^i(X, F) = 0` for every quasi-coherent `𝒪_X`-module `F` and every `i > 0`;
3. `H^1(X, J) = 0` for every coherent ideal sheaf `J ⊆ 𝒪_X`.

Cohomology is that of the underlying abelian sheaf; ideal sheaves are quasi-coherent ideal
subsheaves of `𝒪_X`. -/
theorem isAffine_tfae_sheafCohomology (X : Scheme.{u}) [IsNoetherian X] :
    List.TFAE
      [IsAffine X,
        ∀ (F : X.Modules) [F.IsQuasicoherent] (i : ℕ), 0 < i →
          IsZero ((sheafCohomology X.toTopCat i).obj
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)),
        ∀ J : QuasicoherentIdealSubsheaf X, IsCoherent J.toModules →
          IsZero ((sheafCohomology X.toTopCat 1).obj
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj J.toModules))] := by
  tfae_have 1 → 2 := fun h F _ i hi => by
    have := h
    exact sheafCohomology_isZero_of_isQuasicoherent_of_isAffine F i hi
  tfae_have 2 → 3 := fun h J _ => by
    have := J.isQuasicoherent
    exact h J.toModules 1 Nat.one_pos
  tfae_have 3 → 1 := fun h => isAffine_of_isZero_H1 fun J => h J (isCoherent_toModules J)
  tfae_finish

end Hartshorne
