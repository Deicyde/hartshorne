/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.KoszulRegularImmersionTopExtDeterminant

/-!
# The conormal classes of a Koszul chart form a frame

Let `i : X ⟶ Y` be a closed immersion with ideal sheaf `I` and `c` a Koszul chart on `V` with
generators `f₁, …, f_r`. The conormal classes `[fⱼ]` form a frame of `i^* I` over `i⁻¹ V`
(`Hartshorne.KoszulImmersion.KoszulChart.isLocalFrame_conormalSection`). On the affine scheme
`Spec Γ(X, i⁻¹ V)` this is the frame `pullbackIdealFrame` of the conormal sheaf, whose sections
are the pullbacks of the generators (`pullbackIdealFrame_freeSection_eq_unit`); it is moved to `X`
along the open immersion `Spec Γ(X, i⁻¹ V) ⟶ X` (`isLocalFrame_of_restrict`), using that the
tautological sections of a finite free module form a frame (`Ringed.isLocalFrame_free_top`).

With the determinant frames this proves the sheaf form of the top-Ext calculation: for a
Koszul-regular closed immersion of codimension `r = s + 1` and a quasi-coherent `M`, the glued
isomorphism `ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_* ℋom(⋀^r(i^* I), i^* M)`
(`Hartshorne.KoszulTarget.sheafExtTopIso`, given on each chart by `sheafExtTopIso_inv_restrict`)
and its determinant form `ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_*((⋀^r(i^* I))^∨ ⊗ i^* M)`
(`sheafExtTopIsoDualTensor`); `⋀^r(i^* I)` is invertible (`isLocallyFreeOfRank_exteriorPower`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace Ringed

section Biproducts

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] {J : Type*} [Fintype J]
  [DecidableEq J] (A : C)

private lemma sigma_ι_isoCoproduct_inv_π' [HasCoproduct (fun _ : J => A)] (i j : J) :
    Sigma.ι (fun _ : J => A) i ≫ (biproduct.isoCoproduct (fun _ : J => A)).inv ≫
      biproduct.π (fun _ : J => A) j = if i = j then 𝟙 A else 0 := by
  rw [biproduct.isoCoproduct_inv, ← Category.assoc, Sigma.ι_desc, biproduct.ι_π]
  split_ifs with h
  · subst h; rfl
  · rfl

omit [DecidableEq J] in
private lemma sum_isoCoproduct_inv_π_sigma_ι' [HasCoproduct (fun _ : J => A)] :
    ∑ i, ((biproduct.isoCoproduct (fun _ : J => A)).inv ≫ biproduct.π (fun _ : J => A) i) ≫
      Sigma.ι (fun _ : J => A) i = 𝟙 _ := by
  have h : ∀ i, Sigma.ι (fun _ : J => A) i =
      biproduct.ι (fun _ : J => A) i ≫ (biproduct.isoCoproduct (fun _ : J => A)).hom := by
    intro i
    rw [biproduct.isoCoproduct_hom, biproduct.ι_desc]
  simp_rw [h, Category.assoc, ← Preadditive.comp_sum]
  simp_rw [← Category.assoc, ← Preadditive.sum_comp]
  have ht : ∑ j, biproduct.π (fun _ : J => A) j ≫ biproduct.ι (fun _ : J => A) j = 𝟙 _ :=
    IsBilimit.total (biproduct.isBilimit _)
  rw [ht, Category.id_comp, Iso.inv_hom_id]

end Biproducts

section FreeFrameTop

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {I : Type u} [Fintype I] [DecidableEq I]

/-- The `i`-th coordinate projection of a finite free module. -/
private noncomputable def freeProjTop (i : I) :
    (SheafOfModules.free I : SheafOfModules.{u} (ringCatSheafOf R)) ⟶
      SheafOfModules.unit (ringCatSheafOf R) :=
  (biproduct.isoCoproduct (fun _ : I => SheafOfModules.unit (ringCatSheafOf R))).inv ≫
    biproduct.π (fun _ : I => SheafOfModules.unit (ringCatSheafOf R)) i

/-- **The standard sections of a finite free module form a frame over the whole space.** -/
theorem isLocalFrame_free_top :
    IsLocalFrame (SheafOfModules.free I : SheafOfModules.{u} (ringCatSheafOf R)) ⊤
      (fun i => (SheafOfModules.ιFree (R := ringCatSheafOf R) i).val.app (op ⊤)
        (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op ⊤) from
          (1 : R.obj.obj (op ⊤)))) := by
  intro V h
  have hres : ∀ i, (SheafOfModules.free I : SheafOfModules.{u} (ringCatSheafOf R)).val.presheaf.map
      (homOfLE h).op ((SheafOfModules.ιFree (R := ringCatSheafOf R) i).val.app (op ⊤)
        (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op ⊤) from
          (1 : R.obj.obj (op ⊤)))) =
      (SheafOfModules.ιFree (R := ringCatSheafOf R) i).val.app (op V)
        (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op V) from
          (1 : R.obj.obj (op V))) := by
    intro i
    refine (PresheafOfModules.naturality_apply (SheafOfModules.ιFree (R := ringCatSheafOf R)
      i).val (homOfLE h).op _).symm.trans ?_
    change (SheafOfModules.ιFree (R := ringCatSheafOf R) i).val.app (op V)
      (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op V) from
        R.obj.map (homOfLE h).op 1) = _
    rw [map_one]
  have hsmul : ∀ i (a : R.obj.obj (op V)),
      a • (SheafOfModules.ιFree (R := ringCatSheafOf R) (I := I) i).val.app (op V)
        (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op V) from
          (1 : R.obj.obj (op V))) =
      (SheafOfModules.ιFree (R := ringCatSheafOf R) (I := I) i).val.app (op V)
        (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op V) from a) := by
    intro i a
    refine (((SheafOfModules.ιFree (R := ringCatSheafOf R) (I := I) i).val.app
      (op V)).hom.map_smul a _).symm.trans ?_
    congr 1
    exact mul_one a
  have hF : ∀ a, localFrameMap (SheafOfModules.free I : SheafOfModules.{u} (ringCatSheafOf R))
      (fun i => (SheafOfModules.ιFree (R := ringCatSheafOf R) i).val.app (op ⊤)
        (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op ⊤) from
          (1 : R.obj.obj (op ⊤)))) h a =
      ∑ i, (SheafOfModules.ιFree (R := ringCatSheafOf R) (I := I) i).val.app (op V)
        (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op V) from a i) := by
    intro a
    rw [localFrameMap_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hres, hsmul]
  have hπι : ∀ (i j : I) (r : R.obj.obj (op V)),
      (freeProjTop (R := R) j).val.app (op V)
        ((SheafOfModules.ιFree (R := ringCatSheafOf R) (I := I) i).val.app (op V)
          (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op V) from r)) =
        if i = j then r else 0 := by
    intro i j r
    have := congrArg (fun φ => φ.val.app (op V)
      (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op V) from r))
      (sigma_ι_isoCoproduct_inv_π' (SheafOfModules.unit (ringCatSheafOf R)) i j)
    refine this.trans ?_
    split_ifs <;> rfl
  have hsum : ∀ s : (SheafOfModules.free I : SheafOfModules.{u} (ringCatSheafOf R)).val.obj
      (op V), ∑ i, (SheafOfModules.ιFree (R := ringCatSheafOf R) (I := I) i).val.app (op V)
        ((freeProjTop (R := R) i).val.app (op V) s) = s := by
    intro s
    let ev : ((SheafOfModules.free I : SheafOfModules.{u} (ringCatSheafOf R)) ⟶
        SheafOfModules.free I) →+
        (SheafOfModules.free I : SheafOfModules.{u} (ringCatSheafOf R)).val.obj (op V) :=
      { toFun φ := φ.val.app (op V) s
        map_zero' := rfl
        map_add' _ _ := rfl }
    have := congrArg ev
      (sum_isoCoproduct_inv_π_sigma_ι' (SheafOfModules.unit (ringCatSheafOf R)) (J := I))
    rw [map_sum] at this
    exact this
  have hΨ : ∀ a : I → R.obj.obj (op V), (fun j => (show R.obj.obj (op V) from
      (freeProjTop (R := R) j).val.app (op V)
        (localFrameMap (SheafOfModules.free I : SheafOfModules.{u} (ringCatSheafOf R))
          (fun i => (SheafOfModules.ιFree (R := ringCatSheafOf R) i).val.app (op ⊤)
            (show (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op ⊤) from
              (1 : R.obj.obj (op ⊤)))) h a))) = a := by
    intro a
    funext j
    rw [hF, map_sum]
    simp_rw [hπι]
    exact (Finset.sum_eq_single j (fun k _ hk => if_neg hk)
      (fun h' => absurd (Finset.mem_univ j) h')).trans (if_pos rfl)
  refine ⟨fun a b hab => ?_, fun s => ⟨fun j => (freeProjTop (R := R) j).val.app (op V) s, ?_⟩⟩
  · rw [← hΨ a, ← hΨ b, hab]
  · exact (hF _).trans (hsum s)

/-- The tautological sections of a finite free module form a frame over the whole space. -/
theorem isLocalFrame_freeSection :
    IsLocalFrame (SheafOfModules.free I : SheafOfModules.{u} (ringCatSheafOf R)) ⊤
      (fun i => (SheafOfModules.freeSection (R := ringCatSheafOf R) i).val (op ⊤)) :=
  isLocalFrame_free_top

end FreeFrameTop

end Ringed

namespace KoszulImmersion

open AlgebraicGeometry Koszul KoszulConormal Ringed

/-- **Frames along an open immersion.** A frame over `Z` of the restriction of `F` along an
open immersion `f : Z ⟶ X` is a frame of `F` over the image of `f`. -/
theorem isLocalFrame_of_restrict {Z X : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    (F : X.Modules) {ι : Type*} [Fintype ι] (e : ι → Γ(F.restrict f, ⊤))
    (he : IsLocalFrame (R := Z.sheaf) (F.restrict f) ⊤ e) :
    IsLocalFrame (R := X.sheaf) F (f ''ᵁ ⊤) (fun k => (show Γ(F, f ''ᵁ ⊤) from e k)) := by
  intro W hW
  obtain ⟨W', rfl⟩ : ∃ W', f ''ᵁ W' = W := ⟨f ⁻¹ᵁ W, by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.image_top_eq_opensRange]
    exact inf_eq_right.mpr hW⟩
  have key : ⇑(localFrameMap (R := X.sheaf) F (fun k => (show Γ(F, f ''ᵁ ⊤) from e k)) hW) =
      ⇑(localFrameMap (R := Z.sheaf) (F.restrict f) e (le_top : W' ≤ ⊤)) ∘
        (Equiv.piCongrRight fun _ => (f.appIso W').commRingCatIsoToRingEquiv.toEquiv) := by
    funext a
    rw [Function.comp_apply, localFrameMap_apply, localFrameMap_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ = (f.appIso W').inv ((f.appIso W').hom (a k)) •
      (show Γ(F, f ''ᵁ W') from (F.restrict f).val.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op
        (e k))
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]
    rfl
  rw [key]
  exact (he W' le_top).comp (Equiv.bijective _)

variable {Y X : Scheme.{u}} {i : X ⟶ Y} {r : ℕ} [IsClosedImmersion i]

/-- The ideal-sheaf section of a generator is the restriction of the corresponding element of
`I(U)`. -/
lemma KoszulChart.idealSection_eq_generatorSection {V : Y.Opens} (c : KoszulChart i r V)
    (j : Fin r) :
    haveI := c.hV.isOpenImmersion_fromSpec
    (closedImmersionIdealSheaf i).presheaf.map
      (homOfLE (image_fromSpec_top (⟨V, c.hV⟩ : Y.affineOpens)).ge).op
        (show Γ(closedImmersionIdealSheaf i, c.hV.fromSpec ''ᵁ ⊤) from
          generatorSection i ⟨V, c.hV⟩ c.hI j) = c.idealSection j := by
  apply closedImmersionIdealSheafι_app_injective
  rw [KoszulChart.ι_idealSection]
  refine (PresheafOfModules.naturality_apply (closedImmersionIdealSheafι i).val _ _).trans ?_
  exact idealSectionsToSections_generatorSection i ⟨V, c.hV⟩ c.hI j

-- Unfolding the pullback of the ideal-sheaf frame on sections recurses deeply, as in
-- `pullbackIdealFrame_freeSection_eq_unit`.
set_option maxRecDepth 10000 in
/-- **The conormal classes of a chart form a frame.** For a Koszul chart on `V` with generators
`f₁, …, f_r`, the classes `[fⱼ]` form a frame of `i^* I` over `i⁻¹ V`. -/
theorem KoszulChart.isLocalFrame_conormalSection {V : Y.Opens} (c : KoszulChart i r V) :
    IsLocalFrame (R := X.sheaf) ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))
      (i ⁻¹ᵁ V) (fun j => c.conormalSection j) := by
  classical
  let U : Y.affineOpens := ⟨V, c.hV⟩
  let V' := closedImmersionAffinePreimage i U
  have : IsOpenImmersion V'.2.fromSpec := V'.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hspec := IsLocalFrame.of_iso (@asIso _ _ _ _ (pullbackIdealFrame i U c.hI c.hf)
    (isIso_pullbackIdealFrame i U c.hI c.hf))
    (isLocalFrame_freeSection (R := (Spec (preimageSections i U)).sheaf) (I := ULift.{u} (Fin r)))
  have hX := isLocalFrame_of_restrict V'.2.fromSpec
    ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)) _ hspec
  have hle : i ⁻¹ᵁ V ≤ V'.2.fromSpec ''ᵁ ⊤ := (image_fromSpec_top V').ge
  have hT : V'.2.fromSpec ''ᵁ ⊤ ≤ i ⁻¹ᵁ (U.2.fromSpec ''ᵁ ⊤) := by
    rw [image_fromSpec_top V', image_fromSpec_top U]
  have hfr := (hX.restrictLE hle).reindex Equiv.ulift.{u}.symm
  refine (congrArg (IsLocalFrame _ _) (funext fun j => ?_)).mp hfr
  have h1 := pullbackIdealFrame_freeSection_eq_unit i U c.hI c.hf j hT
  change ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)).val.presheaf.map
      (homOfLE hle).op ((SheafOfModules.sectionsMap (pullbackIdealFrame i U c.hI c.hf)
        (SheafOfModules.freeSection (ULift.up j))).val (op ⊤)) = c.conormalSection j
  rw [h1]
  erw [presheaf_map_map_apply ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)) _ _
    (homOfLE (hle.trans hT)).op]
  rw [KoszulChart.conormalSection, ← c.idealSection_eq_generatorSection j]
  exact (PresheafOfModules.naturality_apply ((Scheme.Modules.pullbackPushforwardAdjunction
    i).unit.app (closedImmersionIdealSheaf i)).val (homOfLE (image_fromSpec_top U).ge).op _).symm

end KoszulImmersion

namespace KoszulTarget

open AlgebraicGeometry Koszul KoszulImmersion KoszulConormal Ringed

variable {Y X : Scheme.{u}} {i : X ⟶ Y} {s : ℕ}

/-- The Koszul charts of a Koszul-regular immersion cover `Y`. -/
lemma exists_koszulChart (h : IsKoszulRegularImmersion i (s + 1)) (y : Y) :
    ∃ (V : Y.Opens) (_ : KoszulChart i (s + 1) V), y ∈ V := by
  obtain ⟨U, hyU, f, hI, hf⟩ := h.exists_isKoszulRegular y
  exact ⟨U, ⟨U.2, f, hI, hf⟩, hyU⟩

/-- **The top sheaf Ext of a Koszul-regular immersion.** For a Koszul-regular closed immersion
`i : X ⟶ Y` of codimension `s + 1` with ideal sheaf `I` and a quasi-coherent `𝒪_Y`-module `M`,
the isomorphism `ℰxt^{s+1}_Y(i_* 𝒪_X, M) ≅ i_* ℋom(⋀^{s+1}(i^* I), i^* M)` obtained by gluing,
over the Koszul charts `c`, the local top-Ext isomorphisms followed by evaluation at the
determinant frames `[f₁] ∧ ⋯ ∧ [f_{s+1}]` (`sheafExtTopIso_inv_restrict`). It involves no choice
of charts or generators. -/
noncomputable def sheafExtTopIso (h : IsKoszulRegularImmersion i (s + 1)) (M : Y.Modules)
    [M.IsQuasicoherent] :
    (Ringed.sheafExt (R := Y.sheaf) ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf)) (s + 1)).obj M ≅
        (Scheme.Modules.pushforward i).obj (moduleSheafHom (R := X.sheaf)
          (moduleSheafExteriorPower (R := X.sheaf) (s + 1)
            ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)))
          ((Scheme.Modules.pullback i).obj M)) :=
  haveI := h.isClosedImmersion
  sheafExtIsoOfFrames M _ (fun _ c => c.conormalFrame)
    (fun _ c => c.isLocalFrame_conormalFrame c.isLocalFrame_conormalSection)
    (fun _ c W b hb => c.conormalFrame_restrict W b hb)
    (fun _ c g hIg hfg Q hg => c.conormalFrame_of_eq_vecMul g hIg hfg Q hg)
    (exists_koszulChart h)

/-- On a Koszul chart `c` on `V`, the inverse of `sheafExtTopIso` is evaluation at the
determinant frame `[f₁] ∧ ⋯ ∧ [f_{s+1}]` followed by the inverse of the local top-Ext
isomorphism of `c`. -/
lemma sheafExtTopIso_inv_restrict (h : IsKoszulRegularImmersion i (s + 1)) (M : Y.Modules)
    [M.IsQuasicoherent] [IsClosedImmersion i] {V : Y.Opens} (c : KoszulChart i (s + 1) V) :
    (moduleRestrict V).map (sheafExtTopIso h M).inv =
      frameEval i _ ((Scheme.Modules.pullback i).obj M) c.conormalFrame ≫ (c.topExtIso M).inv :=
  sheafExtIsoOfFrames_inv_restrict M _ (fun _ c => c.conormalFrame)
    (fun _ c => c.isLocalFrame_conormalFrame c.isLocalFrame_conormalSection)
    (fun _ c W b hb => c.conormalFrame_restrict W b hb)
    (fun _ c g hIg hfg Q hg => c.conormalFrame_of_eq_vecMul g hIg hfg Q hg)
    (exists_koszulChart h) c

/-- The top exterior power of the conormal sheaf of a Koszul-regular immersion is invertible. -/
lemma isLocallyFreeOfRank_exteriorPower (h : IsKoszulRegularImmersion i (s + 1)) :
    IsLocallyFreeOfRank (R := X.sheaf) (moduleSheafExteriorPower (R := X.sheaf) (s + 1)
      ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))) 1 := by
  have := h.isClosedImmersion
  refine isLocallyFreeOfRank_of_isLocalFrame fun x => ?_
  obtain ⟨V, c, hV⟩ := exists_koszulChart h (i.base x)
  exact ⟨i ⁻¹ᵁ V, fun _ => c.conormalFrame, hV,
    (c.isLocalFrame_conormalFrame c.isLocalFrame_conormalSection).reindex
      ⟨fun _ => PUnit.unit, fun _ => ⟨0⟩, fun _ => Subsingleton.elim _ _, fun _ => rfl⟩⟩

/-- **The top sheaf Ext of a Koszul-regular immersion, determinant form.** For a Koszul-regular
closed immersion `i : X ⟶ Y` of codimension `r = s + 1` with ideal sheaf `I` and a
quasi-coherent `𝒪_Y`-module `M`,
`ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_*((⋀^r(i^* I))^∨ ⊗ i^* M)`, where `i^* I` is the conormal sheaf
`I/I²` on `X`: `sheafExtTopIso` followed by `ℋom(L, N) ≅ L^∨ ⊗ N` for the invertible
`L = ⋀^r(i^* I)`. -/
noncomputable def sheafExtTopIsoDualTensor (h : IsKoszulRegularImmersion i (s + 1))
    (M : Y.Modules) [M.IsQuasicoherent] :
    (Ringed.sheafExt (R := Y.sheaf) ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf)) (s + 1)).obj M ≅
        (Scheme.Modules.pushforward i).obj (moduleSheafTensor (R := X.sheaf)
          (moduleSheafDual (R := X.sheaf) (moduleSheafExteriorPower (R := X.sheaf) (s + 1)
            ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))))
          ((Scheme.Modules.pullback i).obj M)) :=
  sheafExtTopIso h M ≪≫ (Scheme.Modules.pushforward i).mapIso
    (moduleSheafDualTensorIso (R := X.sheaf) _ _
      (isLocallyFreeOfRank_exteriorPower h).isFiniteLocallyFree).symm

end KoszulTarget

end Hartshorne
