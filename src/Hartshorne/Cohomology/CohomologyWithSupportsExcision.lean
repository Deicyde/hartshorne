/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.CohomologyWithSupports

/-!
# Excision for cohomology with supports

Hartshorne, *Algebraic Geometry*, III, Exercise 2.3(f), p. 212.

Let `Y` be a closed subset of a topological space `X` and `V` an open subset containing `Y`.
Restriction of sections `Γ_Y(X,F) ⟶ Γ_{Y}(V,F|_V)` is a natural isomorphism for every abelian
sheaf `F` (`Hartshorne.supportedSectionsRestrict`, an isomorphism by
`Hartshorne.supportedSectionsRestrict_isIso`): a section supported in `Y` that vanishes on `V`
vanishes on the cover `{V, X \ Y}`, and a section on `V` supported in `Y` glues with `0` on
`X \ Y`.

Restriction to `V` is exact and preserves injectives, so it carries an injective resolution of
`F` to one of `F|_V`; hence `R^n(G ∘ (-)|_V)(F) ≅ (R^n G)(F|_V)` naturally for every additive
functor `G` on abelian sheaves on `V` (`Hartshorne.openRestrictRightDerivedIso`). Combining the
two gives the excision isomorphism `H^n_Y(X,F) ≅ H^n_Y(V,F|_V)`
(`Hartshorne.cohomologyWithSupportsExcisionIso`).
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Hartshorne

variable {X : TopCat.{u}}

section RightDerivedRestrict

variable (V : Opens X) (G : (TopCat.of V).Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u})
  [G.Additive]

/-- `R^n(G ∘ (-)|_V)(F) ≅ (R^n G)(F|_V)`, computed from the restriction to `V` of the chosen
injective resolution of `F`. -/
noncomputable def openRestrictRightDerivedObjIso (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    ((openRestrict V ⋙ G).rightDerived n).obj F ≅
      (G.rightDerived n).obj ((openRestrict V).obj F) :=
  (injectiveResolution F).isoRightDerivedObj (openRestrict V ⋙ G) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (openRestrict V ⋙ G)) _).app
        (injectiveResolution F).cocomplex).symm ≪≫
    ((openRestrictInjectiveResolution V (injectiveResolution F)).isoRightDerivedObj G n).symm

/-- Naturality of `Hartshorne.openRestrictRightDerivedObjIso`. -/
lemma openRestrictRightDerivedObjIso_naturality {F F' : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ F')
    (n : ℕ) :
    ((openRestrict V ⋙ G).rightDerived n).map f ≫ (openRestrictRightDerivedObjIso V G F' n).hom =
      (openRestrictRightDerivedObjIso V G F n).hom ≫
        (G.rightDerived n).map ((openRestrict V).map f) := by
  have comm := InjectiveResolution.desc_commutes_zero f (injectiveResolution F')
    (injectiveResolution F)
  simp only [openRestrictRightDerivedObjIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc f _ _ _ comm]
  rw [← cancel_mono ((openRestrictInjectiveResolution V
    (injectiveResolution F')).isoRightDerivedObj G n).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [InjectiveResolution.isoRightDerivedObj_hom_naturality ((openRestrict V).map f)
    (openRestrictInjectiveResolution V (injectiveResolution F))
    (openRestrictInjectiveResolution V (injectiveResolution F'))
    (((openRestrict V).mapHomologicalComplex _).map
      (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F)))
    (openRestrictInjectiveResolution_comm V f _ _ _ comm)]
  simp only [Iso.inv_hom_id_assoc, Functor.comp_map, Functor.mapIso_hom]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Right derived functors commute with restriction to an open subset `V`:
`R^n(G ∘ (-)|_V) ≅ (R^n G) ∘ (-)|_V` for every additive functor `G` on abelian sheaves on `V`. -/
noncomputable def openRestrictRightDerivedIso (n : ℕ) :
    (openRestrict V ⋙ G).rightDerived n ≅ openRestrict V ⋙ G.rightDerived n :=
  NatIso.ofComponents (fun F => openRestrictRightDerivedObjIso V G F n)
    (fun f => openRestrictRightDerivedObjIso_naturality V G f n)

end RightDerivedRestrict

section Excision

variable (Y : Set X) (hY : IsClosed Y) (V : Opens X)

/-- The closed subset `Y ∩ V` of the open subspace `V`. -/
abbrev closedInOpen : Set (TopCat.of V) := Subtype.val ⁻¹' Y

include hY in
/-- `Y ∩ V` is closed in `V`. -/
lemma isClosed_closedInOpen : IsClosed (closedInOpen Y V) :=
  hY.preimage continuous_subtype_val

/-- Restriction of global sections of `F` to `V`, as global sections of `F|_V`. -/
noncomputable def restrictToOpenGlobalSections :
    sheafSectionsOver (X := X) ⊤ ⟶ openRestrict V ⋙ sheafSectionsOver (X := TopCat.of V) ⊤ where
  app F := F.obj.map (homOfLE (le_top : V.isOpenEmbedding.functor.obj ⊤ ≤ ⊤)).op
  naturality _ _ f := (f.hom.naturality _).symm

/-- The image in `X` of `V \ Y` lies in `X \ Y`. -/
lemma functor_obj_closedComplement_le :
    V.isOpenEmbedding.functor.obj
        (closedComplement (closedInOpen Y V) (isClosed_closedInOpen Y hY V)) ≤
      closedComplement Y hY := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy

/-- `V ∩ (X \ Y)` lies in the image in `X` of `V \ Y`. -/
lemma inf_closedComplement_le :
    V.isOpenEmbedding.functor.obj ⊤ ⊓ closedComplement Y hY ≤
      V.isOpenEmbedding.functor.obj
        (closedComplement (closedInOpen Y V) (isClosed_closedInOpen Y hY V)) := by
  rintro _ ⟨⟨y, -, rfl⟩, hy⟩
  exact ⟨y, hy, rfl⟩

/-- A section supported in `Y`, restricted to `V`, vanishes on `V \ Y`. -/
lemma supportedSectionsι_restrict_comp_eq_zero (F : X.Sheaf AddCommGrpCat.{u}) :
    ((supportedSectionsι Y hY).app F ≫ (restrictToOpenGlobalSections V).app F) ≫
      (restrictGlobalSections
        (closedComplement (closedInOpen Y V) (isClosed_closedInOpen Y hY V))).app
          ((openRestrict V).obj F) = 0 := by
  have h : (restrictToOpenGlobalSections V).app F ≫
      (restrictGlobalSections
        (closedComplement (closedInOpen Y V) (isClosed_closedInOpen Y hY V))).app
          ((openRestrict V).obj F) =
      (restrictGlobalSections (closedComplement Y hY)).app F ≫
        F.obj.map (homOfLE (functor_obj_closedComplement_le Y hY V)).op := by
    simp only [restrictGlobalSections_app]
    erw [← F.obj.map_comp, ← F.obj.map_comp]
    rfl
  have h0 : (supportedSectionsι Y hY).app F ≫ (restrictGlobalSections (closedComplement Y hY)).app F
      = 0 := (supportedSectionsSC Y hY F).zero
  rw [Category.assoc, h]
  exact ((reassoc_of% h0) _).trans zero_comp

/-- The component at `F` of restriction `Γ_Y(X,F) ⟶ Γ_{Y ∩ V}(V,F|_V)`. -/
noncomputable def supportedSectionsRestrictApp (F : X.Sheaf AddCommGrpCat.{u}) :
    (supportedSections Y hY).obj F ⟶
      (supportedSections (closedInOpen Y V) (isClosed_closedInOpen Y hY V)).obj
        ((openRestrict V).obj F) :=
  (supportedSectionsSC_exact (closedInOpen Y V) (isClosed_closedInOpen Y hY V)
    ((openRestrict V).obj F)).lift ((supportedSectionsι Y hY).app F ≫
      (restrictToOpenGlobalSections V).app F) (supportedSectionsι_restrict_comp_eq_zero Y hY V F)

/-- `Hartshorne.supportedSectionsRestrictApp` lifts restriction to `V`. -/
@[reassoc]
lemma supportedSectionsRestrictApp_ι (F : X.Sheaf AddCommGrpCat.{u}) :
    supportedSectionsRestrictApp Y hY V F ≫
        (supportedSectionsι (closedInOpen Y V) (isClosed_closedInOpen Y hY V)).app
          ((openRestrict V).obj F) =
      (supportedSectionsι Y hY).app F ≫ (restrictToOpenGlobalSections V).app F :=
  ShortComplex.Exact.lift_f _ _ _

/-- Restriction `Γ_Y(X,F) ⟶ Γ_{Y ∩ V}(V,F|_V)` of sections supported in `Y`, natural in `F`. -/
noncomputable def supportedSectionsRestrict :
    supportedSections Y hY ⟶
      openRestrict V ⋙ supportedSections (closedInOpen Y V) (isClosed_closedInOpen Y hY V) where
  app F := supportedSectionsRestrictApp Y hY V F
  naturality F G f := by
    have : Mono ((supportedSectionsι (closedInOpen Y V) (isClosed_closedInOpen Y hY V)).app
        ((openRestrict V).obj G)) := supportedSectionsSC_mono_f _ _ _
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [← cancel_mono ((supportedSectionsι (closedInOpen Y V) (isClosed_closedInOpen Y hY V)).app
        ((openRestrict V).obj G)), Category.assoc, Category.assoc, supportedSectionsRestrictApp_ι,
      (supportedSectionsι (closedInOpen Y V) (isClosed_closedInOpen Y hY V)).naturality,
      supportedSectionsRestrictApp_ι_assoc, (supportedSectionsι Y hY).naturality_assoc]
    congr 1
    exact (restrictToOpenGlobalSections V).naturality f

/-- On underlying sections, `Hartshorne.supportedSectionsRestrict` is restriction to `V`. -/
lemma supportedSectionsRestrict_app_ι (F : X.Sheaf AddCommGrpCat.{u})
    (a : (supportedSections Y hY).obj F) :
    (supportedSectionsι (closedInOpen Y V) (isClosed_closedInOpen Y hY V)).app
        ((openRestrict V).obj F) ((supportedSectionsRestrict Y hY V).app F a) =
      F.obj.map (homOfLE (le_top : V.isOpenEmbedding.functor.obj ⊤ ≤ ⊤)).op
        ((supportedSectionsι Y hY).app F a) :=
  ConcreteCategory.congr_hom (supportedSectionsRestrictApp_ι Y hY V F) a

variable {Y hY V} in
/-- If `Y ⊆ V`, then `V` and `X \ Y` cover `X`. -/
lemma top_le_functor_obj_top_sup (hYV : Y ⊆ V) :
    ⊤ ≤ V.isOpenEmbedding.functor.obj ⊤ ⊔ closedComplement Y hY := by
  rintro x -
  rw [Opens.mem_sup]
  by_cases hx : x ∈ Y
  · left
    rw [Opens.isOpenEmbedding_obj_top]
    exact hYV hx
  · exact Or.inr hx

/-- For `Y ⊆ V`, restriction `Γ_Y(X,F) ⟶ Γ_{Y ∩ V}(V,F|_V)` is an isomorphism. -/
theorem supportedSectionsRestrict_isIso (hYV : Y ⊆ V) :
    IsIso (supportedSectionsRestrict Y hY V) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F => ?_
  set Y' := closedInOpen Y V
  set hY' := isClosed_closedInOpen Y hY V
  set W := V.isOpenEmbedding.functor.obj ⊤
  set U := closedComplement Y hY
  have hι : Function.Injective ((supportedSectionsι Y hY).app F) :=
    (AddCommGrpCat.mono_iff_injective _).1 (supportedSectionsSC_mono_f Y hY F)
  have hι' : Function.Injective ((supportedSectionsι Y' hY').app ((openRestrict V).obj F)) :=
    (AddCommGrpCat.mono_iff_injective _).1 (supportedSectionsSC_mono_f Y' hY' _)
  have hzero : ∀ a, F.obj.map (homOfLE (le_top : U ≤ ⊤)).op
      ((supportedSectionsι Y hY).app F a) = 0 :=
    fun a => ConcreteCategory.congr_hom (supportedSectionsSC Y hY F).zero a
  have hzero' : ∀ b, F.obj.map (V.isOpenEmbedding.functor.map
      (homOfLE (le_top : closedComplement Y' hY' ≤ ⊤))).op
      ((supportedSectionsι Y' hY').app ((openRestrict V).obj F) b) = 0 :=
    fun b => ConcreteCategory.congr_hom (supportedSectionsSC Y' hY' ((openRestrict V).obj F)).zero b
  have hcover := top_le_functor_obj_top_sup (hY := hY) hYV
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · rw [injective_iff_map_eq_zero ((supportedSectionsRestrict Y hY V).app F).hom]
    intro a ha
    have ha' : (supportedSectionsRestrict Y hY V).app F a = 0 := ha
    have h₁ : F.obj.map (homOfLE (le_top : W ≤ ⊤)).op ((supportedSectionsι Y hY).app F a) = 0 := by
      rw [← supportedSectionsRestrict_app_ι, ha', map_zero]
      rfl
    apply hι
    rw [map_zero]
    refine F.eq_of_locally_eq₂ (homOfLE le_top : W ⟶ ⊤) (homOfLE le_top : U ⟶ ⊤) hcover _ 0
      (h₁.trans (map_zero _).symm) ((hzero a).trans (map_zero _).symm)
  · intro b
    have hb := hzero' b
    generalize htb : (supportedSectionsι Y' hY').app ((openRestrict V).obj F) b = t at hb
    have ht : ∀ (O : Opens X) (i : O ⟶ W), O ≤ U → F.obj.map i.op t = 0 := by
      intro O i hO
      have hc : F.obj.map (V.isOpenEmbedding.functor.map
          (homOfLE (le_top : closedComplement Y' hY' ≤ ⊤))).op ≫
          F.obj.map (homOfLE ((le_inf i.le hO).trans (inf_closedComplement_le Y hY V))).op =
          F.obj.map i.op := by
        erw [← F.obj.map_comp]
        rfl
      calc F.obj.map i.op t = (F.obj.map (V.isOpenEmbedding.functor.map
          (homOfLE (le_top : closedComplement Y' hY' ≤ ⊤))).op ≫
          F.obj.map (homOfLE ((le_inf i.le hO).trans
            (inf_closedComplement_le Y hY V))).op) t := (ConcreteCategory.congr_hom hc t).symm
        _ = 0 := by
          erw [ConcreteCategory.comp_apply, hb, map_zero]
    let sf : ∀ i : Bool, ToType (F.obj.obj (op (cond i W U))) := fun i =>
      match i with
      | true => t
      | false => 0
    have hcover' : (⊤ : Opens X) ≤ iSup (fun i : Bool => cond i W U) := by
      rw [iSup_bool_eq]
      exact hcover
    have compat : TopCat.Presheaf.IsCompatible F.obj (fun i : Bool => cond i W U) sf := by
      rintro (_ | _) (_ | _)
      · simp [sf]
      · simp only [sf, map_zero]
        exact (ht _ _ inf_le_left).symm
      · simp only [sf, map_zero]
        exact ht _ _ inf_le_right
      · rfl
    obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' (fun i : Bool => cond i W U) ⊤
      (fun _ => homOfLE le_top) hcover' sf compat
    obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff _).1 (supportedSectionsSC_exact Y hY F) s
      (hs false)
    refine ⟨a, hι' ?_⟩
    erw [supportedSectionsRestrict_app_ι, ha, htb]
    exact hs true

/-- For `Y ⊆ V`, restriction `Γ_Y(X,-) ≅ Γ_{Y ∩ V}(V,(-)|_V)`. -/
noncomputable def supportedSectionsRestrictIso (hYV : Y ⊆ V) :
    supportedSections Y hY ≅
      openRestrict V ⋙ supportedSections (closedInOpen Y V) (isClosed_closedInOpen Y hY V) :=
  have := supportedSectionsRestrict_isIso Y hY V hYV
  asIso (supportedSectionsRestrict Y hY V)

/-- **Hartshorne III, Exercise 2.3(f)** (excision). Let `Y ⊆ X` be closed and `V` an open
subset containing `Y`. There are natural isomorphisms `H^n_Y(X,F) ≅ H^n_Y(V,F|_V)`.
The isomorphism constructed here is the derived functor of restriction
`Γ_Y(X,-) ⟶ Γ_Y(V,(-)|_V)`, followed by the identification of the derived functors of
`Γ_Y(V,(-)|_V)` with `H^n_Y(V,(-)|_V)` (`Hartshorne.cohomologyWithSupportsExcisionIso_hom`). -/
noncomputable def cohomologyWithSupportsExcisionIso (hYV : Y ⊆ V) (n : ℕ) :
    cohomologyWithSupports Y hY n ≅
      openRestrict V ⋙
        cohomologyWithSupports (closedInOpen Y V) (isClosed_closedInOpen Y hY V) n :=
  { hom := NatTrans.rightDerived (supportedSectionsRestrictIso Y hY V hYV).hom n
    inv := NatTrans.rightDerived (supportedSectionsRestrictIso Y hY V hYV).inv n
    hom_inv_id := by
      refine (NatTrans.rightDerived_comp _ _ n).symm.trans ?_
      rw [Iso.hom_inv_id]
      exact NatTrans.rightDerived_id _ n
    inv_hom_id := by
      refine (NatTrans.rightDerived_comp _ _ n).symm.trans ?_
      rw [Iso.inv_hom_id]
      exact NatTrans.rightDerived_id _ n } ≪≫
    openRestrictRightDerivedIso V _ n

/-- The excision isomorphism is induced by restriction `Γ_Y(X,-) ⟶ Γ_Y(V,(-)|_V)`. -/
lemma cohomologyWithSupportsExcisionIso_hom (hYV : Y ⊆ V) (n : ℕ) :
    (cohomologyWithSupportsExcisionIso Y hY V hYV n).hom =
      NatTrans.rightDerived (supportedSectionsRestrict Y hY V) n ≫
        (openRestrictRightDerivedIso V _ n).hom :=
  rfl

end Excision

end Hartshorne
