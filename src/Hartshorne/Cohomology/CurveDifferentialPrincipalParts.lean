/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.GenericDifferentials
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular
import Hartshorne.Scheme.FiniteCurveDivisorPullback

/-!
# The differential principal-parts resolution of a curve

Hartshorne, *Algebraic Geometry*, III.7, the residue discussion on p. 248.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace Hartshorne

universe u

section Nontrivial

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- On a nonsingular curve, `Ω_{K/k} ≠ 0`: otherwise `K/k` would be formally unramified, hence
algebraic, while `trdeg_k K = 1`. -/
theorem functionFieldDifferentials_nontrivial (hX : X.IsNonsingularCurve k) :
    Nontrivial (functionFieldDifferentials (X ↘ Spec (.of k))) := by
  set f := X ↘ Spec (.of k)
  have hf : FiniteType f := ⟨hX.locallyOfFiniteType, hX.quasiCompact⟩
  let _ : LocallyOfFiniteType f := hf.1
  let := functionFieldAlgebra f
  obtain ⟨z, hz⟩ := hX.exists_ne_genericPoint
  have hzc : IsClosed ({z} : Set X) :=
    (hX.isClosed_singleton_iff_coheight_eq_one z).2 ((hX.coheight_eq_one_iff z).2 hz)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨d, -, htr, hdim⟩ := exists_dim_eq_trdeg_of_isAffineOpen f hf U hU
  have hn : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by
    simpa using hX.topologicalKrullDim_eq_one
  have h1 := DifferentialsNonsingular.ringKrullDim_stalk_of_isClosed f hf hn z hzc
  rw [hdim ⟨z, hzU⟩ hzc] at h1
  have hd : d = 1 := by exact_mod_cast h1
  have hUle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let φU : k →+* Γ(X, U) :=
    (f.appLE ⊤ U hUle).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k Γ(X, U) := φU.toAlgebra
  have hinv : Function.Surjective (Scheme.ΓSpecIso (.of k)).inv := by
    intro w
    exact ⟨(Scheme.ΓSpecIso (.of k)).hom w, by simp⟩
  have hφU : φU.FiniteType :=
    (f.finiteType_appLE (isAffineOpen_top _) hU hUle).comp
      (RingHom.FiniteType.of_surjective _ hinv)
  have : Algebra.FiniteType k Γ(X, U) := hφU
  have : IsScalarTower k Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change X.presheaf.germ (f ⁻¹ᵁ ⊤) (genericPoint X) trivial
          (f.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv a)) = X.germToFunctionField U (φU a)
      simp only [φU, RingHom.coe_comp, Function.comp_apply]
      convert
        (X.presheaf.germ_res_apply (homOfLE hUle) (genericPoint X)
          (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
            (by simpa using (inferInstance : Nonempty U)))
          (f.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv a))).symm using 1
      simp [Scheme.Hom.appLE, Scheme.germToFunctionField, Scheme.functionField]
      rfl
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    .of_isLocalization _ (nonZeroDivisors Γ(X, U))
  have : Algebra.EssFiniteType k X.functionField := .comp k Γ(X, U) X.functionField
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have : Algebra.FormallyUnramified k X.functionField := ⟨hsub⟩
  have : Algebra.IsSeparable k X.functionField :=
    Algebra.FormallyUnramified.isSeparable k X.functionField
  have h0 : Algebra.trdeg k X.functionField = 0 := trdeg_eq_zero
  rw [htr, hd] at h0
  exact one_ne_zero h0

end Nontrivial

/-- The structure sheaf of a scheme, as a module over itself. -/
abbrev unitModuleOf (Y : Scheme.{u}) : Y.Modules :=
  SheafOfModules.unit Y.ringCatSheaf

section Injective

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
  (W : X.Opens)
  (β : (Scheme.relativeDifferentials f).restrict W.ι ≅
    unitModuleOf W.toScheme)

/-- The unit section of the structure sheaf over `V`, as a section of a module. -/
def unitSection {Y : Scheme.{u}} (V : Y.Opens) : Γ(unitModuleOf Y, V) :=
  (1 : Γ(Y, V))

/-- A section of the structure sheaf, regarded as a section of a module, as a function. -/
def unitSectionVal {Y : Scheme.{u}} {V : Y.Opens} (a : Γ(unitModuleOf Y, V)) : Γ(Y, V) :=
  a

theorem smul_unitSection {Y : Scheme.{u}} {V : Y.Opens} (a : Γ(unitModuleOf Y, V)) :
    unitSectionVal a • unitSection V = a :=
  mul_one (unitSectionVal a)

theorem unitSection_res {Y : Scheme.{u}} {V V' : Y.Opens} (i : V' ⟶ V) :
    (unitModuleOf Y).presheaf.map i.op (unitSection V) = unitSection V' :=
  map_one (Y.presheaf.map i.op).hom

/-- A generator of `Ω_{X/k}` over an open set `W` on which it is trivialized. -/
def localGenerator : Γ(Scheme.relativeDifferentials f, W.ι ''ᵁ ⊤) :=
  β.inv.app ⊤ (unitSection ⊤)

omit [IsIntegral X] in
theorem image_le_image_top (V : W.toScheme.Opens) : W.ι ''ᵁ V ≤ W.ι ''ᵁ ⊤ :=
  W.ι.image_mono le_top

omit [IsIntegral X] in
/-- Over an open subset of `W`, every section of `Ω_{X/k}` is a multiple of the generator. -/
theorem eq_smul_localGenerator (V : W.toScheme.Opens)
    (s : Γ(Scheme.relativeDifferentials f, W.ι ''ᵁ V)) :
    s = (W.ι.appIso V).inv (unitSectionVal (β.hom.app V s)) •
      (Scheme.relativeDifferentials f).presheaf.map (homOfLE (image_le_image_top W V)).op
        (localGenerator f W β) := by
  have h1 : β.inv.app V (β.hom.app V s) = s :=
    congrArg (fun φ => (Scheme.Modules.Hom.app φ V) s) β.hom_inv_id
  have h4 := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf β.inv).naturality (homOfLE (le_top : V ≤ ⊤)).op)
    (unitSection ⊤)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, unitSection_res] at h4
  show @Eq Γ((Scheme.relativeDifferentials f).restrict W.ι, V) s _
  refine h1.symm.trans ?_
  conv_lhs => rw [← smul_unitSection (β.hom.app V s)]
  rw [Scheme.Modules.Hom.app_smul]
  erw [h4]
  rfl

/-- The image of a section over an open subset of `W` is a multiple of that of the generator. -/
theorem differentialsGenericValue_eq_smul (V : W.toScheme.Opens)
    (s : Γ(Scheme.relativeDifferentials f, W.ι ''ᵁ V)) (y : W.ι ''ᵁ V) :
    differentialsGenericValue f s y =
      genericGerm _ y ((W.ι.appIso V).inv (unitSectionVal (β.hom.app V s))) •
        differentialsGenericValue f (localGenerator f W β) ⟨y.1, image_le_image_top W V y.2⟩ := by
  conv_lhs => rw [eq_smul_localGenerator f W β V s]
  rw [differentialsToGeneric_smul, differentialsToGeneric_res]

omit [IsIntegral X] in
theorem mem_of_mem_image_top {y : X} (hy : y ∈ W.ι ''ᵁ ⊤) : y ∈ W := by
  rwa [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at hy

/-- The image of the generator in `Ω_{K/k}` is nonzero. -/
theorem differentialsGenericValue_localGenerator_ne_zero
    [Nontrivial (functionFieldDifferentials f)] (y : W.ι ''ᵁ ⊤) :
    differentialsGenericValue f (localGenerator f W β) y ≠ 0 := by
  intro h0
  have hD : ∀ (V : W.toScheme.Opens) (a : Γ(X, W.ι ''ᵁ V)) (z : W.ι ''ᵁ V),
      functionFieldD f (genericGerm _ z a) = 0 := by
    intro V a z
    refine (differentialsToGeneric_d f _ a z).symm.trans
      ((differentialsGenericValue_eq_smul f W β V _ z).trans ?_)
    rw [differentialsGenericValue_eq f _ _ y, h0, smul_zero]
  have hK : ∀ z : X.functionField, functionFieldD f z = 0 := by
    intro z
    obtain ⟨W', hW', e, rfl⟩ := X.presheaf.exists_germ_eq z
    have hmem : genericPoint X ∈ W.ι ''ᵁ (W.ι ⁻¹ᵁ W') := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact ⟨genericPoint_mem_of_mem (mem_of_mem_image_top W y.2), hW'⟩
    have h := hD _ (X.presheaf.map (homOfLE (W.ι.image_preimage_le W')).op e) ⟨_, hmem⟩
    rwa [genericGerm_res] at h
  have hle : Submodule.span X.functionField (Set.range (functionFieldD f)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact hK z
  rw [span_range_functionFieldD, top_le_iff] at hle
  obtain ⟨a, ha⟩ := exists_ne (0 : functionFieldDifferentials f)
  exact ha ((Submodule.mem_bot _).1 (hle.symm ▸ Submodule.mem_top))

include β in
/-- Over a nonempty open subset of a trivializing open set, `Ω_{X/k} ⟶ Ω_K` is injective. -/
theorem differentialsToGeneric_app_injective_of_iso [Nontrivial (functionFieldDifferentials f)]
    (V : W.toScheme.Opens) (y₀ : W.ι ''ᵁ V) :
    Function.Injective ((differentialsToGeneric f).app (W.ι ''ᵁ V)).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hval : differentialsGenericValue f s y₀ = 0 := by
    have h : differentialsGenericValue f s = 0 := hs
    rw [h]
    rfl
  rw [differentialsGenericValue_eq_smul f W β V s y₀] at hval
  have hgerm := (smul_eq_zero.1 hval).resolve_right
    (differentialsGenericValue_localGenerator_ne_zero f W β _)
  have hr : (W.ι.appIso V).inv (unitSectionVal (β.hom.app V s)) = 0 :=
    germ_injective_of_isIntegral X _ _ (hgerm.trans (map_zero _).symm)
  rw [eq_smul_localGenerator f W β V s, hr, zero_smul]

end Injective

section GlobalInjective

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))

/-- A trivialization of an invertible module identifies its restriction with the structure
sheaf. -/
noncomputable def restrictIsoUnitOfFree {M : X.Modules} {W : X.Opens}
    (α : M.restrict W.ι ≅ SheafOfModules.free (ULift.{u} (Fin 1))) :
    M.restrict W.ι ≅ unitModuleOf W.toScheme :=
  α ≪≫ Limits.coproductUniqueIso (C := SheafOfModules W.toScheme.ringCatSheaf)
    (fun _ : ULift.{u} (Fin 1) => SheafOfModules.unit W.toScheme.ringCatSheaf)

/-- **Injectivity of `Ω_{X/k} ⟶ Ω_K`** on every open set, for `Ω_{X/k}` invertible and
`Ω_{K/k} ≠ 0`. -/
theorem differentialsToGeneric_app_injective [Nontrivial (functionFieldDifferentials f)]
    (hfree : (Scheme.relativeDifferentials f).IsLocallyFreeOfRank 1) (U : X.Opens) :
    Function.Injective ((differentialsToGeneric f).app U).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  choose W hW α using hfree
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj (Scheme.relativeDifferentials f)
  let Ui : U → X.Opens := fun x => (W x).ι ''ᵁ ((W x).ι ⁻¹ᵁ U)
  have hUi : ∀ x, Ui x ≤ U := fun x => (W x).ι.image_preimage_le U
  refine TopCat.Sheaf.eq_of_locally_eq' F Ui U (fun x => homOfLE (hUi x)) ?_ s 0 fun x => ?_
  · intro y hy
    refine Opens.mem_iSup.2 ⟨⟨y, hy⟩, ?_⟩
    change y ∈ (W y).ι ''ᵁ ((W y).ι ⁻¹ᵁ U)
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨hW y, hy⟩
  · have hx : (x : X) ∈ Ui x := by
      change (x : X) ∈ (W x).ι ''ᵁ ((W x).ι ⁻¹ᵁ U)
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact ⟨hW x, x.2⟩
    rw [map_zero]
    refine differentialsToGeneric_app_injective_of_iso f (W x)
      (restrictIsoUnitOfFree (α x).some) _ ⟨x, hx⟩ ?_
    have h := ConcreteCategory.congr_hom
      ((Scheme.Modules.Hom.mapPresheaf (differentialsToGeneric f)).naturality
        (homOfLE (hUi x)).op) s
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    refine (h.trans ?_).trans (map_zero ((differentialsToGeneric f).app _).hom).symm
    change (genericConstantModule (functionFieldDifferentials f)).presheaf.map _
      (((differentialsToGeneric f).app U).hom s) = 0
    rw [hs, map_zero]

end GlobalInjective

end Hartshorne
