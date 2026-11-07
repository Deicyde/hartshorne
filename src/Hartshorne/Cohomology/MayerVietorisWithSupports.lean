/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.CohomologyWithSupports

/-!
# Mayer–Vietoris sequence for cohomology with supports

Hartshorne, *Algebraic Geometry*, III, Exercise 2.4, p. 212.

For closed subsets `Y₁, Y₂` of a topological space `X` and an abelian sheaf `F`, the sequence of
support functors
`0 ⟶ Γ_{Y₁∩Y₂}(X,F) ⟶ Γ_{Y₁}(X,F) ⊕ Γ_{Y₂}(X,F) ⟶ Γ_{Y₁∪Y₂}(X,F)`,
with maps `s ↦ (s, s)` and `(s₁, s₂) ↦ s₁ - s₂`, is exact (`Hartshorne.mayerVietorisSC_exact`,
`Hartshorne.mayerVietorisSC_mono_f`), and for flasque `F` the last map is surjective
(`Hartshorne.mayerVietorisSC_shortExact_of_isFlasque`).

The Mayer–Vietoris sequence
`0 ⟶ H^0_{Y₁∩Y₂}(X,F) ⟶ H^0_{Y₁}(X,F) ⊕ H^0_{Y₂}(X,F) ⟶ H^0_{Y₁∪Y₂}(X,F) ⟶ H^1_{Y₁∩Y₂}(X,F) ⟶ ⋯`
is formed by the natural transformations `Hartshorne.mayerVietorisι`, `Hartshorne.mayerVietorisπ`
and `Hartshorne.mayerVietorisδ`, and it is exact (`Hartshorne.mayerVietorisι_mono`,
`Hartshorne.mayerVietoris_exact₂`, `Hartshorne.mayerVietoris_exact₃`,
`Hartshorne.mayerVietoris_exact₁`).

For an injective resolution `I` of `F` the sheaves `I^k` are flasque, so the sequence of support
functors applied to `I` is a short exact sequence of complexes, and the Mayer–Vietoris sequence is
its homology sequence.
-/
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Hartshorne

variable {X : TopCat.{u}}

section SupportFunctors

instance supportedSectionsι_mono (Y : Set X) (hY : IsClosed Y) :
    Mono (supportedSectionsι Y hY) :=
  inferInstanceAs (Mono (kernel.ι _))

lemma supportedSectionsι_comp_restrict (Y : Set X) (hY : IsClosed Y) :
    supportedSectionsι Y hY ≫ restrictGlobalSections (closedComplement Y hY) = 0 :=
  kernel.condition _

/-- For closed subsets `Y' ⊆ Y`, the inclusion `Γ_{Y'}(X,-) ⟶ Γ_Y(X,-)`. -/
noncomputable def supportedSectionsMap {Y' Y : Set X} (hY' : IsClosed Y') (hY : IsClosed Y)
    (h : Y' ⊆ Y) : supportedSections Y' hY' ⟶ supportedSections Y hY :=
  kernel.lift _ (supportedSectionsι Y' hY') (by
    have hle : closedComplement Y hY ≤ closedComplement Y' hY' := Set.compl_subset_compl.mpr h
    have e : restrictGlobalSections (closedComplement Y hY) =
        restrictGlobalSections (closedComplement Y' hY') ≫
          Functor.whiskerLeft _ ((evaluation _ _).map (homOfLE hle).op) := by
      ext F : 2
      change F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← Functor.map_comp]
      rfl
    rw [e, ← Category.assoc, supportedSectionsι_comp_restrict, zero_comp])

@[reassoc (attr := simp)]
lemma supportedSectionsMap_ι {Y' Y : Set X} (hY' : IsClosed Y') (hY : IsClosed Y) (h : Y' ⊆ Y) :
    supportedSectionsMap hY' hY h ≫ supportedSectionsι Y hY = supportedSectionsι Y' hY' :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
lemma supportedSectionsMap_app_ι {Y' Y : Set X} (hY' : IsClosed Y') (hY : IsClosed Y)
    (h : Y' ⊆ Y) (F : X.Sheaf AddCommGrpCat.{u}) :
    (supportedSectionsMap hY' hY h).app F ≫ (supportedSectionsι Y hY).app F =
      (supportedSectionsι Y' hY').app F := by
  rw [← NatTrans.comp_app, supportedSectionsMap_ι]

instance supportedSectionsι_app_mono (Y : Set X) (hY : IsClosed Y) (F : X.Sheaf AddCommGrpCat.{u}) :
    Mono ((supportedSectionsι Y hY).app F) :=
  supportedSectionsSC_mono_f Y hY F

lemma supportedSectionsι_app_injective (Y : Set X) (hY : IsClosed Y)
    (F : X.Sheaf AddCommGrpCat.{u}) : Function.Injective ((supportedSectionsι Y hY).app F) :=
  (AddCommGrpCat.mono_iff_injective _).1 inferInstance

/-- A global section restricting to zero on `X \ Y` comes from `Γ_Y(X,F)`. -/
lemma exists_supportedSectionsι_app_eq (Y : Set X) (hY : IsClosed Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (s : F.obj.obj (op ⊤))
    (hs : F.obj.map (homOfLE (le_top : closedComplement Y hY ≤ ⊤)).op s = 0) :
    ∃ t, (supportedSectionsι Y hY).app F t = s :=
  (ShortComplex.ab_exact_iff _).1 (supportedSectionsSC_exact Y hY F) s hs

lemma supportedSectionsι_app_restrict (Y : Set X) (hY : IsClosed Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (t : (supportedSections Y hY).obj F) :
    F.obj.map (homOfLE (le_top : closedComplement Y hY ≤ ⊤)).op
      ((supportedSectionsι Y hY).app F t) = 0 :=
  congrArg (fun φ => φ t) (supportedSectionsSC Y hY F).zero

variable {Y₁ Y₂ : Set X} (hY₁ : IsClosed Y₁) (hY₂ : IsClosed Y₂)

lemma supportedSectionsMap_comm :
    supportedSectionsMap (hY₁.inter hY₂) hY₁ Set.inter_subset_left ≫
        supportedSectionsMap hY₁ (hY₁.union hY₂) Set.subset_union_left =
      supportedSectionsMap (hY₁.inter hY₂) hY₂ Set.inter_subset_right ≫
        supportedSectionsMap hY₂ (hY₁.union hY₂) Set.subset_union_right := by
  rw [← cancel_mono (supportedSectionsι _ (hY₁.union hY₂))]
  simp

/-- The sequence `0 ⟶ Γ_{Y₁∩Y₂}(X,F) ⟶ Γ_{Y₁}(X,F) ⊕ Γ_{Y₂}(X,F) ⟶ Γ_{Y₁∪Y₂}(X,F)`, with maps
`s ↦ (s, s)` and `(s₁, s₂) ↦ s₁ - s₂`. -/
@[simps]
noncomputable abbrev mayerVietorisSC (F : X.Sheaf AddCommGrpCat.{u}) :
    ShortComplex AddCommGrpCat.{u} where
  X₁ := (supportedSections (Y₁ ∩ Y₂) (hY₁.inter hY₂)).obj F
  X₂ := (supportedSections Y₁ hY₁).obj F ⊞ (supportedSections Y₂ hY₂).obj F
  X₃ := (supportedSections (Y₁ ∪ Y₂) (hY₁.union hY₂)).obj F
  f := biprod.lift ((supportedSectionsMap (hY₁.inter hY₂) hY₁ Set.inter_subset_left).app F)
    ((supportedSectionsMap (hY₁.inter hY₂) hY₂ Set.inter_subset_right).app F)
  g := biprod.desc ((supportedSectionsMap hY₁ (hY₁.union hY₂) Set.subset_union_left).app F)
    (-(supportedSectionsMap hY₂ (hY₁.union hY₂) Set.subset_union_right).app F)
  zero := by
    rw [biprod.lift_desc, Preadditive.comp_neg, ← NatTrans.comp_app, ← NatTrans.comp_app,
      supportedSectionsMap_comm hY₁ hY₂, add_neg_cancel]

lemma biprod_ab_eq {A B : AddCommGrpCat.{u}} (x : (A ⊞ B : AddCommGrpCat.{u})) :
    x = (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) x) +
      (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) x) := by
  have h := ConcreteCategory.congr_hom (biprod.total (X := A) (Y := B)) x
  rw [AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] at h
  exact h.symm

private lemma ab_neg_apply {A B : AddCommGrpCat.{u}} (f : A ⟶ B) (x : A) : (-f) x = -(f x) :=
  rfl

lemma mayerVietorisSC_g_apply (F : X.Sheaf AddCommGrpCat.{u})
    (a : (supportedSections Y₁ hY₁).obj F) (b : (supportedSections Y₂ hY₂).obj F) :
    (supportedSectionsι _ (hY₁.union hY₂)).app F ((mayerVietorisSC hY₁ hY₂ F).g
      ((biprod.inl : _ ⟶ _ ⊞ (supportedSections Y₂ hY₂).obj F) a +
        (biprod.inr : _ ⟶ (supportedSections Y₁ hY₁).obj F ⊞ _) b)) =
      (supportedSectionsι Y₁ hY₁).app F a - (supportedSectionsι Y₂ hY₂).app F b := by
  have e1 := ConcreteCategory.congr_hom
    (biprod.inl_desc ((supportedSectionsMap hY₁ (hY₁.union hY₂) Set.subset_union_left).app F)
      (-(supportedSectionsMap hY₂ (hY₁.union hY₂) Set.subset_union_right).app F)) a
  have e2 := ConcreteCategory.congr_hom
    (biprod.inr_desc ((supportedSectionsMap hY₁ (hY₁.union hY₂) Set.subset_union_left).app F)
      (-(supportedSectionsMap hY₂ (hY₁.union hY₂) Set.subset_union_right).app F)) b
  rw [ConcreteCategory.comp_apply] at e1 e2
  have h1 := ConcreteCategory.congr_hom (supportedSectionsMap_app_ι hY₁ (hY₁.union hY₂)
    Set.subset_union_left F) a
  have h2 := ConcreteCategory.congr_hom (supportedSectionsMap_app_ι hY₂ (hY₁.union hY₂)
    Set.subset_union_right F) b
  rw [ConcreteCategory.comp_apply] at h1 h2
  change (supportedSectionsι _ (hY₁.union hY₂)).app F
    ((biprod.desc ((supportedSectionsMap hY₁ (hY₁.union hY₂) Set.subset_union_left).app F)
      (-(supportedSectionsMap hY₂ (hY₁.union hY₂) Set.subset_union_right).app F))
      ((biprod.inl : _ ⟶ _ ⊞ (supportedSections Y₂ hY₂).obj F) a +
        (biprod.inr : _ ⟶ (supportedSections Y₁ hY₁).obj F ⊞ _) b)) = _
  rw [map_add, e1, e2, map_add, ab_neg_apply, map_neg, h1, h2, sub_eq_add_neg]

/-- The sequence `0 ⟶ Γ_{Y₁∩Y₂}(X,F) ⟶ Γ_{Y₁}(X,F) ⊕ Γ_{Y₂}(X,F) ⟶ Γ_{Y₁∪Y₂}(X,F)` is exact. -/
theorem mayerVietorisSC_exact (F : X.Sheaf AddCommGrpCat.{u}) :
    (mayerVietorisSC hY₁ hY₂ F).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  obtain ⟨a, b, rfl⟩ : ∃ (a : (supportedSections Y₁ hY₁).obj F)
      (b : (supportedSections Y₂ hY₂).obj F),
      x = (biprod.inl : _ ⟶ _ ⊞ (supportedSections Y₂ hY₂).obj F) a +
        (biprod.inr : _ ⟶ (supportedSections Y₁ hY₁).obj F ⊞ _) b :=
    ⟨_, _, biprod_ab_eq x⟩
  have hab : (supportedSectionsι Y₁ hY₁).app F a = (supportedSectionsι Y₂ hY₂).app F b := by
    have := mayerVietorisSC_g_apply hY₁ hY₂ F a b
    rw [hx] at this
    erw [map_zero] at this
    exact sub_eq_zero.1 this.symm
  have hs₁ := (restrict_closedComplement_eq_zero_iff Y₁ hY₁ F _).1
    (supportedSectionsι_app_restrict Y₁ hY₁ F a)
  have hs₂ := (restrict_closedComplement_eq_zero_iff Y₂ hY₂ F _).1
    (supportedSectionsι_app_restrict Y₂ hY₂ F b)
  rw [← hab] at hs₂
  obtain ⟨c, hc⟩ := exists_supportedSectionsι_app_eq (Y₁ ∩ Y₂) (hY₁.inter hY₂) F _
    ((restrict_closedComplement_eq_zero_iff (Y₁ ∩ Y₂) (hY₁.inter hY₂) F _).2
      (Set.subset_inter hs₁ hs₂))
  refine ⟨c, ?_⟩
  change (biprod.lift ((supportedSectionsMap (hY₁.inter hY₂) hY₁ Set.inter_subset_left).app F)
    ((supportedSectionsMap (hY₁.inter hY₂) hY₂ Set.inter_subset_right).app F)) c = _
  have hfst : (biprod.fst : _ ⟶ (supportedSections Y₁ hY₁).obj F)
      ((biprod.lift ((supportedSectionsMap (hY₁.inter hY₂) hY₁ Set.inter_subset_left).app F)
        ((supportedSectionsMap (hY₁.inter hY₂) hY₂ Set.inter_subset_right).app F)) c) = a := by
    apply supportedSectionsι_app_injective
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, biprod.lift_fst_assoc,
      supportedSectionsMap_app_ι, hc]
  have hsnd : (biprod.snd : _ ⟶ (supportedSections Y₂ hY₂).obj F)
      ((biprod.lift ((supportedSectionsMap (hY₁.inter hY₂) hY₁ Set.inter_subset_left).app F)
        ((supportedSectionsMap (hY₁.inter hY₂) hY₂ Set.inter_subset_right).app F)) c) = b := by
    apply supportedSectionsι_app_injective
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, biprod.lift_snd_assoc,
      supportedSectionsMap_app_ι, hc, hab]
  rw [biprod_ab_eq ((biprod.lift
    ((supportedSectionsMap (hY₁.inter hY₂) hY₁ Set.inter_subset_left).app F)
    ((supportedSectionsMap (hY₁.inter hY₂) hY₂ Set.inter_subset_right).app F)) c), hfst, hsnd]

/-- `Γ_{Y₁∩Y₂}(X,F) ⟶ Γ_{Y₁}(X,F) ⊕ Γ_{Y₂}(X,F)` is injective. -/
instance mayerVietorisSC_mono_f (F : X.Sheaf AddCommGrpCat.{u}) :
    Mono (mayerVietorisSC hY₁ hY₂ F).f := by
  have : Mono ((mayerVietorisSC hY₁ hY₂ F).f ≫ biprod.fst ≫ (supportedSectionsι Y₁ hY₁).app F) := by
    dsimp only [mayerVietorisSC]
    rw [biprod.lift_fst_assoc, supportedSectionsMap_app_ι]
    infer_instance
  exact mono_of_mono _ (biprod.fst ≫ (supportedSectionsι Y₁ hY₁).app F)

/-- For a flasque sheaf `F`, `Γ_{Y₁}(X,F) ⊕ Γ_{Y₂}(X,F) ⟶ Γ_{Y₁∪Y₂}(X,F)` is surjective. -/
theorem mayerVietorisSC_epi_g_of_isFlasque (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFlasque] :
    Epi (mayerVietorisSC hY₁ hY₂ F).g := by
  have resres : ∀ {V₁ V₂ V₃ : Opens X} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (z : F.obj.obj (op V₁)),
      F.obj.map (homOfLE h₂).op (F.obj.map (homOfLE h₁).op z) =
        F.obj.map (homOfLE (h₂.trans h₁)).op z := fun h₁ h₂ z => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [AddCommGrpCat.epi_iff_surjective]
  intro t
  set s : ToType (F.obj.obj (op ⊤)) := (supportedSectionsι _ (hY₁.union hY₂)).app F t with hs_def
  have hs := supportedSectionsι_app_restrict _ (hY₁.union hY₂) F t
  let U : Bool → Opens X := fun i => bif i then closedComplement Y₂ hY₂ else closedComplement Y₁ hY₁
  let W := closedComplement (Y₁ ∩ Y₂) (hY₁.inter hY₂)
  let sf : ∀ i, ToType (F.obj.obj (op (U i))) := fun i => match i with
    | false => 0
    | true => F.obj.map (homOfLE (le_top : closedComplement Y₂ hY₂ ≤ ⊤)).op s
  have hU : U false ⊓ U true ≤ closedComplement (Y₁ ∪ Y₂) (hY₁.union hY₂) :=
    fun x hx h => h.elim hx.1 hx.2
  have hU' : U true ⊓ U false ≤ closedComplement (Y₁ ∪ Y₂) (hY₁.union hY₂) :=
    fun x hx h => h.elim hx.2 hx.1
  have hcompat : TopCat.Presheaf.IsCompatible F.obj U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · change F.obj.map (homOfLE inf_le_left).op 0 =
        F.obj.map (homOfLE inf_le_right).op (F.obj.map (homOfLE le_top).op s)
      rw [map_zero]; erw [resres, ← resres le_top hU, hs]; rw [map_zero]
    · change F.obj.map (homOfLE inf_le_left).op (F.obj.map (homOfLE le_top).op s) =
        F.obj.map (homOfLE inf_le_right).op 0
      rw [map_zero]; erw [resres, ← resres le_top hU', hs]; rw [map_zero]
    · rfl
  have hle : ∀ i, U i ≤ W := fun i => by
    cases i
    · exact fun x hx h => hx h.1
    · exact fun x hx h => hx h.2
  have hcover : W ≤ iSup U := by
    intro x hx
    rw [Opens.mem_iSup]
    by_cases h₁ : x ∈ Y₁
    · exact ⟨true, fun h₂ => hx ⟨h₁, h₂⟩⟩
    · exact ⟨false, h₁⟩
  obtain ⟨g, hg, -⟩ := F.existsUnique_gluing' U W (fun i => homOfLE (hle i)) hcover sf hcompat
  obtain ⟨s₁, hs₁⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (TopCat.Presheaf.IsFlasque.epi (F := F.obj) (homOfLE (le_top : W ≤ ⊤)).op) g
  have hg₁ : F.obj.map (homOfLE (le_top : closedComplement Y₁ hY₁ ≤ ⊤)).op s₁ = 0 := by
    have := hg false
    change F.obj.map (homOfLE (hle false)).op g = 0 at this
    rw [← hs₁] at this
    erw [resres] at this
    exact this
  have hg₂ : F.obj.map (homOfLE (le_top : closedComplement Y₂ hY₂ ≤ ⊤)).op (s₁ - s) = 0 := by
    have := hg true
    change F.obj.map (homOfLE (hle true)).op g =
      F.obj.map (homOfLE (le_top : closedComplement Y₂ hY₂ ≤ ⊤)).op s at this
    rw [← hs₁] at this
    erw [resres] at this
    rw [map_sub, this, sub_self]
  obtain ⟨a, ha⟩ := exists_supportedSectionsι_app_eq Y₁ hY₁ F s₁ hg₁
  obtain ⟨b, hb⟩ := exists_supportedSectionsι_app_eq Y₂ hY₂ F (s₁ - s) hg₂
  refine ⟨(biprod.inl : _ ⟶ _ ⊞ (supportedSections Y₂ hY₂).obj F) a +
    (biprod.inr : _ ⟶ (supportedSections Y₁ hY₁).obj F ⊞ _) b,
    supportedSectionsι_app_injective _ (hY₁.union hY₂) F ?_⟩
  erw [mayerVietorisSC_g_apply hY₁ hY₂ F a b, ha, hb]
  exact sub_sub_cancel _ _

/-- For a flasque sheaf `F`, the sequence
`0 ⟶ Γ_{Y₁∩Y₂}(X,F) ⟶ Γ_{Y₁}(X,F) ⊕ Γ_{Y₂}(X,F) ⟶ Γ_{Y₁∪Y₂}(X,F) ⟶ 0` is exact. -/
theorem mayerVietorisSC_shortExact_of_isFlasque (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFlasque] :
    (mayerVietorisSC hY₁ hY₂ F).ShortExact where
  exact := mayerVietorisSC_exact hY₁ hY₂ F
  epi_g := mayerVietorisSC_epi_g_of_isFlasque hY₁ hY₂ F

end SupportFunctors

section Sequence

/-- For closed subsets `Y' ⊆ Y`, the induced map `H^n_{Y'}(X,-) ⟶ H^n_Y(X,-)`. -/
noncomputable def cohomologyWithSupportsOfSubset {Y' Y : Set X} (hY' : IsClosed Y')
    (hY : IsClosed Y) (h : Y' ⊆ Y) (n : ℕ) :
    cohomologyWithSupports Y' hY' n ⟶ cohomologyWithSupports Y hY n :=
  NatTrans.rightDerived (supportedSectionsMap hY' hY h) n

/-- `H^n_Y(X,F)` computed from `Γ_Y(X,I)` for an injective resolution `I` of `F`. -/
noncomputable def cohomologyWithSupportsIsoHomology {Y : Set X} {hY : IsClosed Y}
    {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F) (n : ℕ) :
    (cohomologyWithSupports Y hY n).obj F ≅
      (((supportedSections Y hY).mapHomologicalComplex _).obj I.cocomplex).homology n :=
  I.isoRightDerivedObj _ n

lemma cohomologyWithSupportsOfSubset_app_eq {Y' Y : Set X} (hY' : IsClosed Y')
    (hY : IsClosed Y) (h : Y' ⊆ Y) {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (n : ℕ) :
    (cohomologyWithSupportsOfSubset hY' hY h n).app F =
      (cohomologyWithSupportsIsoHomology I n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (supportedSectionsMap hY' hY h) _).app I.cocomplex) n ≫
        (cohomologyWithSupportsIsoHomology I n).inv :=
  InjectiveResolution.rightDerived_app_eq _ I n

variable {Y₁ Y₂ : Set X} (hY₁ : IsClosed Y₁) (hY₂ : IsClosed Y₂)

/-- The functor `Γ_{Y₁}(X,-) ⊕ Γ_{Y₂}(X,-)`. -/
noncomputable abbrev supportedSectionsBiprod : X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj G := (supportedSections Y₁ hY₁).obj G ⊞ (supportedSections Y₂ hY₂).obj G
  map f := biprod.map ((supportedSections Y₁ hY₁).map f) ((supportedSections Y₂ hY₂).map f)
  map_id G := by apply biprod.hom_ext <;> simp
  map_comp f g := by apply biprod.hom_ext <;> simp

instance supportedSectionsBiprod_additive : (supportedSectionsBiprod hY₁ hY₂).Additive where
  map_add := by
    intros
    apply biprod.hom_ext <;> simp [Preadditive.add_comp, Preadditive.comp_add]

/-- The natural map `Γ_{Y₁∩Y₂}(X,-) ⟶ Γ_{Y₁}(X,-) ⊕ Γ_{Y₂}(X,-)`, `s ↦ (s, s)`. -/
noncomputable def supportedSectionsDiag :
    supportedSections (Y₁ ∩ Y₂) (hY₁.inter hY₂) ⟶ supportedSectionsBiprod hY₁ hY₂ where
  app G := (mayerVietorisSC hY₁ hY₂ G).f
  naturality _ _ f := by apply biprod.hom_ext <;> simp [NatTrans.naturality]

/-- The natural map `Γ_{Y₁}(X,-) ⊕ Γ_{Y₂}(X,-) ⟶ Γ_{Y₁∪Y₂}(X,-)`, `(s₁, s₂) ↦ s₁ - s₂`. -/
noncomputable def supportedSectionsDiff :
    supportedSectionsBiprod hY₁ hY₂ ⟶ supportedSections (Y₁ ∪ Y₂) (hY₁.union hY₂) where
  app G := (mayerVietorisSC hY₁ hY₂ G).g
  naturality _ _ f := by apply biprod.hom_ext' <;> simp [NatTrans.naturality]

/-- The projection `Γ_{Y₁}(X,-) ⊕ Γ_{Y₂}(X,-) ⟶ Γ_{Y₁}(X,-)`. -/
noncomputable def supportedSectionsBiprodFst :
    supportedSectionsBiprod hY₁ hY₂ ⟶ supportedSections Y₁ hY₁ where
  app G := biprod.fst

/-- The projection `Γ_{Y₁}(X,-) ⊕ Γ_{Y₂}(X,-) ⟶ Γ_{Y₂}(X,-)`. -/
noncomputable def supportedSectionsBiprodSnd :
    supportedSectionsBiprod hY₁ hY₂ ⟶ supportedSections Y₂ hY₂ where
  app G := biprod.snd

/-- The inclusion `Γ_{Y₁}(X,-) ⟶ Γ_{Y₁}(X,-) ⊕ Γ_{Y₂}(X,-)`. -/
noncomputable def supportedSectionsBiprodInl :
    supportedSections Y₁ hY₁ ⟶ supportedSectionsBiprod hY₁ hY₂ where
  app G := biprod.inl

/-- The inclusion `Γ_{Y₂}(X,-) ⟶ Γ_{Y₁}(X,-) ⊕ Γ_{Y₂}(X,-)`. -/
noncomputable def supportedSectionsBiprodInr :
    supportedSections Y₂ hY₂ ⟶ supportedSectionsBiprod hY₁ hY₂ where
  app G := biprod.inr

/-- The Mayer–Vietoris sequence of support functors applied degreewise to a complex `K` of
sheaves: `0 ⟶ Γ_{Y₁∩Y₂}(X,K) ⟶ Γ_{Y₁}(X,K) ⊕ Γ_{Y₂}(X,K) ⟶ Γ_{Y₁∪Y₂}(X,K)`. -/
noncomputable def mayerVietorisComplexSC (K : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (supportedSectionsDiag hY₁ hY₂) _).app K)
    ((NatTrans.mapHomologicalComplex (supportedSectionsDiff hY₁ hY₂) _).app K)
    (by
      ext n : 1
      exact (mayerVietorisSC hY₁ hY₂ (K.X n)).zero)

section Components

variable (K : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ)

/-- The projection from the middle term of the Mayer–Vietoris sequence of complexes to
`Γ_{Y₁}(X,K)`. -/
noncomputable def mayerVietorisFst :
    (mayerVietorisComplexSC hY₁ hY₂ K).X₂ ⟶
      ((supportedSections Y₁ hY₁).mapHomologicalComplex _).obj K :=
  (NatTrans.mapHomologicalComplex (supportedSectionsBiprodFst hY₁ hY₂) _).app K

/-- The projection from the middle term of the Mayer–Vietoris sequence of complexes to
`Γ_{Y₂}(X,K)`. -/
noncomputable def mayerVietorisSnd :
    (mayerVietorisComplexSC hY₁ hY₂ K).X₂ ⟶
      ((supportedSections Y₂ hY₂).mapHomologicalComplex _).obj K :=
  (NatTrans.mapHomologicalComplex (supportedSectionsBiprodSnd hY₁ hY₂) _).app K

/-- The inclusion of `Γ_{Y₁}(X,K)` into the middle term of the Mayer–Vietoris sequence of
complexes. -/
noncomputable def mayerVietorisInl :
    ((supportedSections Y₁ hY₁).mapHomologicalComplex _).obj K ⟶
      (mayerVietorisComplexSC hY₁ hY₂ K).X₂ :=
  (NatTrans.mapHomologicalComplex (supportedSectionsBiprodInl hY₁ hY₂) _).app K

/-- The inclusion of `Γ_{Y₂}(X,K)` into the middle term of the Mayer–Vietoris sequence of
complexes. -/
noncomputable def mayerVietorisInr :
    ((supportedSections Y₂ hY₂).mapHomologicalComplex _).obj K ⟶
      (mayerVietorisComplexSC hY₁ hY₂ K).X₂ :=
  (NatTrans.mapHomologicalComplex (supportedSectionsBiprodInr hY₁ hY₂) _).app K

@[reassoc (attr := simp)]
lemma mayerVietorisComplexSC_f_fst :
    (mayerVietorisComplexSC hY₁ hY₂ K).f ≫ mayerVietorisFst hY₁ hY₂ K =
      (NatTrans.mapHomologicalComplex
        (supportedSectionsMap (hY₁.inter hY₂) hY₁ Set.inter_subset_left) _).app K :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma mayerVietorisComplexSC_f_snd :
    (mayerVietorisComplexSC hY₁ hY₂ K).f ≫ mayerVietorisSnd hY₁ hY₂ K =
      (NatTrans.mapHomologicalComplex
        (supportedSectionsMap (hY₁.inter hY₂) hY₂ Set.inter_subset_right) _).app K :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.lift_snd _ _

@[reassoc (attr := simp)]
lemma mayerVietorisInl_g :
    mayerVietorisInl hY₁ hY₂ K ≫ (mayerVietorisComplexSC hY₁ hY₂ K).g =
      (NatTrans.mapHomologicalComplex
        (supportedSectionsMap hY₁ (hY₁.union hY₂) Set.subset_union_left) _).app K :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma mayerVietorisInr_g :
    mayerVietorisInr hY₁ hY₂ K ≫ (mayerVietorisComplexSC hY₁ hY₂ K).g =
      -(NatTrans.mapHomologicalComplex
        (supportedSectionsMap hY₂ (hY₁.union hY₂) Set.subset_union_right) _).app K :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inr_desc _ _

@[reassoc (attr := simp)]
lemma mayerVietorisInl_fst : mayerVietorisInl hY₁ hY₂ K ≫ mayerVietorisFst hY₁ hY₂ K = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inl_fst

@[reassoc (attr := simp)]
lemma mayerVietorisInl_snd : mayerVietorisInl hY₁ hY₂ K ≫ mayerVietorisSnd hY₁ hY₂ K = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inl_snd

@[reassoc (attr := simp)]
lemma mayerVietorisInr_fst : mayerVietorisInr hY₁ hY₂ K ≫ mayerVietorisFst hY₁ hY₂ K = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inr_fst

@[reassoc (attr := simp)]
lemma mayerVietorisInr_snd : mayerVietorisInr hY₁ hY₂ K ≫ mayerVietorisSnd hY₁ hY₂ K = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inr_snd

lemma mayerVietoris_total :
    mayerVietorisFst hY₁ hY₂ K ≫ mayerVietorisInl hY₁ hY₂ K +
      mayerVietorisSnd hY₁ hY₂ K ≫ mayerVietorisInr hY₁ hY₂ K = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.total

end Components

/-- For a complex of injective sheaves, the Mayer–Vietoris sequence of complexes is short exact
in each degree. -/
theorem mayerVietorisComplexSC_degreewise_shortExact
    (K : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ) [∀ n, Injective (K.X n)] (n : ℕ) :
    ((mayerVietorisComplexSC hY₁ hY₂ K).map (HomologicalComplex.eval _ _ n)).ShortExact := by
  have := injectiveAbelianSheaf_isFlasque (K.X n)
  exact mayerVietorisSC_shortExact_of_isFlasque hY₁ hY₂ (K.X n)

/-- For a complex of injective sheaves, the Mayer–Vietoris sequence of complexes is short
exact. -/
theorem mayerVietorisComplexSC_shortExact (K : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ)
    [∀ n, Injective (K.X n)] : (mayerVietorisComplexSC hY₁ hY₂ K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (mayerVietorisComplexSC_degreewise_shortExact hY₁ hY₂ K)

/-- The functor `F ↦ H^n_{Y₁}(X,F) ⊕ H^n_{Y₂}(X,F)`. -/
noncomputable abbrev cohomologyWithSupportsBiprod (n : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj F := (cohomologyWithSupports Y₁ hY₁ n).obj F ⊞ (cohomologyWithSupports Y₂ hY₂ n).obj F
  map f := biprod.map ((cohomologyWithSupports Y₁ hY₁ n).map f)
    ((cohomologyWithSupports Y₂ hY₂ n).map f)
  map_id F := by apply biprod.hom_ext <;> simp
  map_comp f g := by apply biprod.hom_ext <;> simp

/-- The map `H^n_{Y₁∩Y₂}(X,F) ⟶ H^n_{Y₁}(X,F) ⊕ H^n_{Y₂}(X,F)`, `s ↦ (s, s)`, of the
Mayer–Vietoris sequence, natural in `F`. -/
noncomputable def mayerVietorisι (n : ℕ) :
    cohomologyWithSupports (Y₁ ∩ Y₂) (hY₁.inter hY₂) n ⟶
      cohomologyWithSupportsBiprod hY₁ hY₂ n where
  app F := biprod.lift
    ((cohomologyWithSupportsOfSubset (hY₁.inter hY₂) hY₁ Set.inter_subset_left n).app F)
    ((cohomologyWithSupportsOfSubset (hY₁.inter hY₂) hY₂ Set.inter_subset_right n).app F)
  naturality _ _ f := by
    apply biprod.hom_ext <;> simp

/-- The map `H^n_{Y₁}(X,F) ⊕ H^n_{Y₂}(X,F) ⟶ H^n_{Y₁∪Y₂}(X,F)`, `(a, b) ↦ a - b`, of the
Mayer–Vietoris sequence, natural in `F`. -/
noncomputable def mayerVietorisπ (n : ℕ) :
    cohomologyWithSupportsBiprod hY₁ hY₂ n ⟶
      cohomologyWithSupports (Y₁ ∪ Y₂) (hY₁.union hY₂) n where
  app F := biprod.desc
    ((cohomologyWithSupportsOfSubset hY₁ (hY₁.union hY₂) Set.subset_union_left n).app F)
    (-(cohomologyWithSupportsOfSubset hY₂ (hY₁.union hY₂) Set.subset_union_right n).app F)
  naturality _ _ f := by
    apply biprod.hom_ext' <;> simp

variable {hY₁ hY₂} in
/-- `H^n_{Y₁∩Y₂}(X,F)` computed from an injective resolution of `F`. -/
noncomputable def mayerVietorisIso₁ {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (n : ℕ) :
    (cohomologyWithSupports (Y₁ ∩ Y₂) (hY₁.inter hY₂) n).obj F ≅
      (mayerVietorisComplexSC hY₁ hY₂ I.cocomplex).X₁.homology n :=
  I.isoRightDerivedObj _ n

variable {hY₁ hY₂} in
/-- `H^n_{Y₁}(X,F) ⊕ H^n_{Y₂}(X,F)` computed from an injective resolution of `F`. -/
noncomputable def mayerVietorisIso₂ {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (n : ℕ) :
    (cohomologyWithSupportsBiprod hY₁ hY₂ n).obj F ≅
      (mayerVietorisComplexSC hY₁ hY₂ I.cocomplex).X₂.homology n where
  hom := biprod.desc
    ((cohomologyWithSupportsIsoHomology I n).hom ≫
      HomologicalComplex.homologyMap (mayerVietorisInl hY₁ hY₂ I.cocomplex) n)
    ((cohomologyWithSupportsIsoHomology I n).hom ≫
      HomologicalComplex.homologyMap (mayerVietorisInr hY₁ hY₂ I.cocomplex) n)
  inv := biprod.lift
    (HomologicalComplex.homologyMap (mayerVietorisFst hY₁ hY₂ I.cocomplex) n ≫
      (cohomologyWithSupportsIsoHomology I n).inv)
    (HomologicalComplex.homologyMap (mayerVietorisSnd hY₁ hY₂ I.cocomplex) n ≫
      (cohomologyWithSupportsIsoHomology I n).inv)
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst,
        biprod.lift_snd, Category.comp_id, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst,
        biprod.inr_snd, ← HomologicalComplex.homologyMap_comp_assoc, mayerVietorisInl_fst,
        mayerVietorisInl_snd, mayerVietorisInr_fst, mayerVietorisInr_snd,
        HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero, Category.id_comp,
        zero_comp, comp_zero, Iso.hom_inv_id]
  inv_hom_id := by
    rw [biprod.lift_desc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_add, mayerVietoris_total, HomologicalComplex.homologyMap_id]

variable {hY₁ hY₂} in
/-- `H^n_{Y₁∪Y₂}(X,F)` computed from an injective resolution of `F`. -/
noncomputable def mayerVietorisIso₃ {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (n : ℕ) :
    (cohomologyWithSupports (Y₁ ∪ Y₂) (hY₁.union hY₂) n).obj F ≅
      (mayerVietorisComplexSC hY₁ hY₂ I.cocomplex).X₃.homology n :=
  I.isoRightDerivedObj _ n

lemma mayerVietorisι_app_eq {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F) (n : ℕ) :
    (mayerVietorisι hY₁ hY₂ n).app F =
      (mayerVietorisIso₁ I n).hom ≫
        HomologicalComplex.homologyMap (mayerVietorisComplexSC hY₁ hY₂ I.cocomplex).f n ≫
        (mayerVietorisIso₂ I n).inv := by
  apply biprod.hom_ext
  · have h : (mayerVietorisIso₂ (hY₁ := hY₁) (hY₂ := hY₂) I n).inv ≫ biprod.fst =
        HomologicalComplex.homologyMap (mayerVietorisFst hY₁ hY₂ I.cocomplex) n ≫
          (cohomologyWithSupportsIsoHomology I n).inv := biprod.lift_fst _ _
    rw [Category.assoc, Category.assoc, h, ← HomologicalComplex.homologyMap_comp_assoc,
      mayerVietorisComplexSC_f_fst]
    exact (biprod.lift_fst _ _).trans (cohomologyWithSupportsOfSubset_app_eq _ _ _ I n)
  · have h : (mayerVietorisIso₂ (hY₁ := hY₁) (hY₂ := hY₂) I n).inv ≫ biprod.snd =
        HomologicalComplex.homologyMap (mayerVietorisSnd hY₁ hY₂ I.cocomplex) n ≫
          (cohomologyWithSupportsIsoHomology I n).inv := biprod.lift_snd _ _
    rw [Category.assoc, Category.assoc, h, ← HomologicalComplex.homologyMap_comp_assoc,
      mayerVietorisComplexSC_f_snd]
    exact (biprod.lift_snd _ _).trans (cohomologyWithSupportsOfSubset_app_eq _ _ _ I n)

lemma mayerVietorisπ_app_eq {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F) (n : ℕ) :
    (mayerVietorisπ hY₁ hY₂ n).app F =
      (mayerVietorisIso₂ I n).hom ≫
        HomologicalComplex.homologyMap (mayerVietorisComplexSC hY₁ hY₂ I.cocomplex).g n ≫
        (mayerVietorisIso₃ I n).inv := by
  apply biprod.hom_ext'
  · have h : biprod.inl ≫ (mayerVietorisIso₂ (hY₁ := hY₁) (hY₂ := hY₂) I n).hom =
        (cohomologyWithSupportsIsoHomology I n).hom ≫
          HomologicalComplex.homologyMap (mayerVietorisInl hY₁ hY₂ I.cocomplex) n :=
      biprod.inl_desc _ _
    rw [reassoc_of% h, ← HomologicalComplex.homologyMap_comp_assoc, mayerVietorisInl_g]
    exact (biprod.inl_desc _ _).trans (cohomologyWithSupportsOfSubset_app_eq _ _ _ I n)
  · have h : biprod.inr ≫ (mayerVietorisIso₂ (hY₁ := hY₁) (hY₂ := hY₂) I n).hom =
        (cohomologyWithSupportsIsoHomology I n).hom ≫
          HomologicalComplex.homologyMap (mayerVietorisInr hY₁ hY₂ I.cocomplex) n :=
      biprod.inr_desc _ _
    rw [reassoc_of% h, ← HomologicalComplex.homologyMap_comp_assoc, mayerVietorisInr_g]
    erw [HomologicalComplex.homologyMap_neg]
    rw [Preadditive.neg_comp, Preadditive.comp_neg]
    exact (biprod.inr_desc _ _).trans
      (congrArg Neg.neg (cohomologyWithSupportsOfSubset_app_eq _ _ _ I n))

/-- The morphism of Mayer–Vietoris sequences of complexes induced by a cochain map. -/
noncomputable def mayerVietorisComplexSCMap {K L : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ}
    (φ : K ⟶ L) : mayerVietorisComplexSC hY₁ hY₂ K ⟶ mayerVietorisComplexSC hY₁ hY₂ L where
  τ₁ := ((supportedSections (Y₁ ∩ Y₂) (hY₁.inter hY₂)).mapHomologicalComplex _).map φ
  τ₂ := ((supportedSectionsBiprod hY₁ hY₂).mapHomologicalComplex _).map φ
  τ₃ := ((supportedSections (Y₁ ∪ Y₂) (hY₁.union hY₂)).mapHomologicalComplex _).map φ
  comm₁₂ := NatTrans.mapHomologicalComplex_naturality _ _
  comm₂₃ := NatTrans.mapHomologicalComplex_naturality _ _

/-- The connecting morphism `H^n_{Y₁∪Y₂}(X,F) ⟶ H^{n+1}_{Y₁∩Y₂}(X,F)` of the Mayer–Vietoris
sequence, computed from the injective resolution of `F` chosen by `injectiveResolution`. -/
noncomputable def mayerVietorisδApp (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (cohomologyWithSupports (Y₁ ∪ Y₂) (hY₁.union hY₂) n).obj F ⟶
      (cohomologyWithSupports (Y₁ ∩ Y₂) (hY₁.inter hY₂) (n + 1)).obj F :=
  (mayerVietorisIso₃ (injectiveResolution F) n).hom ≫
    (mayerVietorisComplexSC_shortExact hY₁ hY₂ (injectiveResolution F).cocomplex).δ n (n + 1)
      (by simp) ≫
      (mayerVietorisIso₁ (injectiveResolution F) (n + 1)).inv

@[reassoc]
lemma mayerVietorisIso₁_inv_naturality {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    (mayerVietorisIso₁ (hY₁ := hY₁) (hY₂ := hY₂) I n).inv ≫
        (cohomologyWithSupports (Y₁ ∩ Y₂) (hY₁.inter hY₂) n).map f =
      HomologicalComplex.homologyMap (mayerVietorisComplexSCMap hY₁ hY₂ φ).τ₁ n ≫
        (mayerVietorisIso₁ J n).inv :=
  InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ comm _ n

@[reassoc]
lemma mayerVietorisIso₃_hom_naturality {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    (cohomologyWithSupports (Y₁ ∪ Y₂) (hY₁.union hY₂) n).map f ≫ (mayerVietorisIso₃ J n).hom =
      (mayerVietorisIso₃ (hY₁ := hY₁) (hY₂ := hY₂) I n).hom ≫
        HomologicalComplex.homologyMap (mayerVietorisComplexSCMap hY₁ hY₂ φ).τ₃ n :=
  InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm _ n

lemma mayerVietorisδApp_naturality {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ) :
    (cohomologyWithSupports (Y₁ ∪ Y₂) (hY₁.union hY₂) n).map f ≫ mayerVietorisδApp hY₁ hY₂ G n =
      mayerVietorisδApp hY₁ hY₂ F n ≫
        (cohomologyWithSupports (Y₁ ∩ Y₂) (hY₁.inter hY₂) (n + 1)).map f := by
  let φ := InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)
  have comm := InjectiveResolution.desc_commutes_zero f (injectiveResolution G)
    (injectiveResolution F)
  have hδ := HomologicalComplex.HomologySequence.δ_naturality
    (mayerVietorisComplexSCMap hY₁ hY₂ φ)
    (mayerVietorisComplexSC_shortExact hY₁ hY₂ (injectiveResolution F).cocomplex)
    (mayerVietorisComplexSC_shortExact hY₁ hY₂ (injectiveResolution G).cocomplex) n (n + 1)
    (by simp)
  simp only [mayerVietorisδApp, Category.assoc]
  rw [mayerVietorisIso₃_hom_naturality_assoc hY₁ hY₂ f _ _ φ comm n,
    mayerVietorisIso₁_inv_naturality hY₁ hY₂ f _ _ φ comm (n + 1), reassoc_of% hδ]

/-- The connecting morphisms `H^n_{Y₁∪Y₂}(X,F) ⟶ H^{n+1}_{Y₁∩Y₂}(X,F)` of the Mayer–Vietoris
sequence, natural in `F`. -/
noncomputable def mayerVietorisδ (n : ℕ) :
    cohomologyWithSupports (Y₁ ∪ Y₂) (hY₁.union hY₂) n ⟶
      cohomologyWithSupports (Y₁ ∩ Y₂) (hY₁.inter hY₂) (n + 1) where
  app F := mayerVietorisδApp hY₁ hY₂ F n
  naturality _ _ f := mayerVietorisδApp_naturality hY₁ hY₂ f n

lemma mayerVietorisδ_app (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (mayerVietorisδ hY₁ hY₂ n).app F =
      (mayerVietorisIso₃ (injectiveResolution F) n).hom ≫
        (mayerVietorisComplexSC_shortExact hY₁ hY₂ (injectiveResolution F).cocomplex).δ n (n + 1)
          (by simp) ≫
        (mayerVietorisIso₁ (injectiveResolution F) (n + 1)).inv :=
  rfl

/-- The Mayer–Vietoris sequence starts with `0`:
`H^0_{Y₁∩Y₂}(X,F) ⟶ H^0_{Y₁}(X,F) ⊕ H^0_{Y₂}(X,F)` is injective. -/
theorem mayerVietorisι_mono (F : X.Sheaf AddCommGrpCat.{u}) :
    Mono ((mayerVietorisι hY₁ hY₂ 0).app F) := by
  rw [mayerVietorisι_app_eq hY₁ hY₂ (injectiveResolution F)]
  have : Mono ((mayerVietorisComplexSC hY₁ hY₂ (injectiveResolution F).cocomplex).f.f 0) :=
    (mayerVietorisComplexSC_degreewise_shortExact hY₁ hY₂ _ 0).mono_f
  have := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    (mayerVietorisComplexSC hY₁ hY₂ (injectiveResolution F).cocomplex).f 0 (fun i => by simp)
  infer_instance

/-- Exactness of `H^n_{Y₁∩Y₂}(X,F) ⟶ H^n_{Y₁}(X,F) ⊕ H^n_{Y₂}(X,F) ⟶ H^n_{Y₁∪Y₂}(X,F)`. -/
theorem mayerVietoris_exact₂ (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (ShortComplex.mk ((mayerVietorisι hY₁ hY₂ n).app F) ((mayerVietorisπ hY₁ hY₂ n).app F) (by
        rw [mayerVietorisι_app_eq hY₁ hY₂ (injectiveResolution F),
          mayerVietorisπ_app_eq hY₁ hY₂ (injectiveResolution F)]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← HomologicalComplex.homologyMap_comp_assoc, ShortComplex.zero,
          HomologicalComplex.homologyMap_zero, zero_comp, comp_zero])).Exact := by
  have hS := mayerVietorisComplexSC_shortExact hY₁ hY₂ (injectiveResolution F).cocomplex
  refine ShortComplex.exact_of_iso ?_ (hS.homology_exact₂ n)
  refine ShortComplex.isoMk (mayerVietorisIso₁ (injectiveResolution F) n).symm
    (mayerVietorisIso₂ (injectiveResolution F) n).symm
    (mayerVietorisIso₃ (injectiveResolution F) n).symm ?_ ?_
  · simp [mayerVietorisι_app_eq hY₁ hY₂ (injectiveResolution F)]
  · simp [mayerVietorisπ_app_eq hY₁ hY₂ (injectiveResolution F)]

/-- Exactness of `H^n_{Y₁}(X,F) ⊕ H^n_{Y₂}(X,F) ⟶ H^n_{Y₁∪Y₂}(X,F) ⟶ H^{n+1}_{Y₁∩Y₂}(X,F)`. -/
theorem mayerVietoris_exact₃ (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (ShortComplex.mk ((mayerVietorisπ hY₁ hY₂ n).app F) ((mayerVietorisδ hY₁ hY₂ n).app F) (by
        rw [mayerVietorisπ_app_eq hY₁ hY₂ (injectiveResolution F), mayerVietorisδ_app]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [ShortComplex.ShortExact.comp_δ_assoc, zero_comp, comp_zero])).Exact := by
  have hS := mayerVietorisComplexSC_shortExact hY₁ hY₂ (injectiveResolution F).cocomplex
  refine ShortComplex.exact_of_iso ?_ (hS.homology_exact₃ n (n + 1) (by simp))
  refine ShortComplex.isoMk (mayerVietorisIso₂ (injectiveResolution F) n).symm
    (mayerVietorisIso₃ (injectiveResolution F) n).symm
    (mayerVietorisIso₁ (injectiveResolution F) (n + 1)).symm ?_ ?_
  · simp [mayerVietorisπ_app_eq hY₁ hY₂ (injectiveResolution F)]
  · simp [mayerVietorisδ_app]

/-- Exactness of `H^n_{Y₁∪Y₂}(X,F) ⟶ H^{n+1}_{Y₁∩Y₂}(X,F) ⟶ H^{n+1}_{Y₁}(X,F) ⊕
H^{n+1}_{Y₂}(X,F)`. -/
theorem mayerVietoris_exact₁ (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (ShortComplex.mk ((mayerVietorisδ hY₁ hY₂ n).app F) ((mayerVietorisι hY₁ hY₂ (n + 1)).app F)
      (by
        rw [mayerVietorisι_app_eq hY₁ hY₂ (injectiveResolution F), mayerVietorisδ_app]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [ShortComplex.ShortExact.δ_comp_assoc, zero_comp, comp_zero])).Exact := by
  have hS := mayerVietorisComplexSC_shortExact hY₁ hY₂ (injectiveResolution F).cocomplex
  refine ShortComplex.exact_of_iso ?_ (hS.homology_exact₁ n (n + 1) (by simp))
  refine ShortComplex.isoMk (mayerVietorisIso₃ (injectiveResolution F) n).symm
    (mayerVietorisIso₁ (injectiveResolution F) (n + 1)).symm
    (mayerVietorisIso₂ (injectiveResolution F) (n + 1)).symm ?_ ?_
  · simp [mayerVietorisδ_app]
  · simp [mayerVietorisι_app_eq hY₁ hY₂ (injectiveResolution F)]

end Sequence

end Hartshorne
