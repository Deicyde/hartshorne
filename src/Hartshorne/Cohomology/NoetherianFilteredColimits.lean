/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Flasque

/-!
# Filtered colimits on Noetherian spaces

Hartshorne II.1, Exercise 1.11, as used in III.2.8–2.9.

Every open of a Noetherian space is quasi-compact, so finite gluing suffices for the sheaf
condition. Filtered colimits commute with the finite pairwise-intersection limits, hence their
pointwise presheaf colimit is already a sheaf. The canonical colimit comparison is therefore an
isomorphism, natural in both the open and the diagram.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Hartshorne

/-- A cover of an open in a Noetherian space has a finite subcover. -/
private theorem noetherian_exists_finset_iSup
    {X : TopCat.{u}} [NoetherianSpace X] {ι : Type u} (U : ι → Opens X) :
    ∃ s : Finset ι, (⨆ i : s, U i) = ⨆ i, U i := by
  have h : IsCompactElement (⨆ i, U i) :=
    (Opens.isCompactElement_iff _).mpr (NoetherianSpace.isCompact _)
  obtain ⟨s, hs⟩ :=
    (CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup _).mp h ι U le_rfl
  refine ⟨s, le_antisymm (iSup_le fun i : s ↦ le_iSup U i) ?_⟩
  exact hs.trans (Finset.sup_le fun i hi ↦ le_iSup (fun j : s ↦ U j) ⟨i, hi⟩)

section FiniteGluing

variable {X : TopCat.{u}} (P : X.Presheaf (Type u))
variable (hP : ∀ ⦃ι : Type u⦄ [Fintype ι] (U : ι → Opens X)
  (sf : ∀ i, P.obj (op (U i))), TopCat.Presheaf.IsCompatible P U sf →
    ∃! s : P.obj (op (iSup U)), TopCat.Presheaf.IsGluing P U sf s)

include hP in
/-- Finite gluing with a specified union and specified inclusion maps. -/
private theorem finite_existsUnique_gluing'
    {ι : Type u} [Fintype ι] (U : ι → Opens X) (V : Opens X)
    (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (sf : ∀ i, P.obj (op (U i))) (hsf : TopCat.Presheaf.IsCompatible P U sf) :
    ∃! s : P.obj (op V), ∀ i, P.map (iUV i).op s = sf i := by
  have hV : V = iSup U := le_antisymm hcover (iSup_le fun i ↦ (iUV i).le)
  subst V
  have hi : iUV = fun i ↦ Opens.leSupr U i := funext fun i ↦ Subsingleton.elim _ _
  simpa only [hi, TopCat.Presheaf.IsGluing] using hP U sf hsf

include hP in
/-- Agreement on a finite cover implies equality, under finite unique gluing. -/
private theorem finite_eq_of_locally_eq
    {ι : Type u} [Fintype ι] (U : ι → Opens X) (V : Opens X)
    (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U) (s t : P.obj (op V))
    (h : ∀ i, P.map (iUV i).op s = P.map (iUV i).op t) : s = t := by
  let sf : ∀ i, P.obj (op (U i)) := fun i ↦ P.map (iUV i).op s
  have hsf : TopCat.Presheaf.IsCompatible P U sf := by
    intro i j
    dsimp only [sf]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← P.map_comp, ← P.map_comp]
    exact congrArg (fun f : op V ⟶ op (U i ⊓ U j) ↦ P.map f s)
      (Subsingleton.elim _ _)
  obtain ⟨g, hg, huniq⟩ := finite_existsUnique_gluing' P hP U V iUV hcover sf hsf
  exact (huniq s (fun i ↦ rfl)).trans (huniq t (fun i ↦ (h i).symm)).symm

include hP in
/-- A finite-subcover gluing restricts to every member of a compatible family. -/
private theorem finite_isGluing_of_subcover
    {ι : Type u} (U : ι → Opens X) (s : Finset ι)
    (hcover : (⨆ i : s, U i) = iSup U) (sf : ∀ i, P.obj (op (U i)))
    (hsf : TopCat.Presheaf.IsCompatible P U sf) (t : P.obj (op (iSup U)))
    (ht : ∀ i : s, P.map (Opens.leSupr U i).op t = sf i) :
    TopCat.Presheaf.IsGluing P U sf t := by
  classical
  intro j
  let W : s → Opens X := fun i ↦ U j ⊓ U i
  have hW : U j ≤ iSup W := by
    dsimp only [W]
    rw [← inf_iSup_eq, hcover]
    exact le_inf le_rfl (le_iSup U j)
  apply finite_eq_of_locally_eq P hP W (U j) (fun i ↦ homOfLE inf_le_left) hW
  intro i
  have h := (hsf j i).symm
  rw [← ht i, ← ConcreteCategory.comp_apply, ← P.map_comp] at h
  refine Eq.trans ?_ h
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  exact congrArg (fun f : op (iSup U) ⟶ op (W i) ↦ P.map f t)
    (Subsingleton.elim _ _)

include hP in
/-- On a Noetherian space, finite unique gluing implies the full sheaf condition. -/
private theorem noetherian_isSheaf_of_finite_gluing [NoetherianSpace X] :
    P.IsSheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types P).mpr
  intro ι U sf hsf
  obtain ⟨s, hs⟩ := noetherian_exists_finset_iSup U
  obtain ⟨t, ht, huniq⟩ := finite_existsUnique_gluing' P hP (fun i : s ↦ U i)
    (iSup U) (fun i ↦ Opens.leSupr U i) hs.symm.le (fun i ↦ sf i)
    (fun i j ↦ hsf i j)
  refine ⟨t, finite_isGluing_of_subcover P hP U s hs sf hsf t ht, ?_⟩
  intro t' ht'
  exact huniq t' (fun i ↦ ht' i)

end FiniteGluing

/-- The pointwise filtered colimit preserves every finite pairwise-intersection limit. -/
private theorem pointwise_filtered_colimit_preserves_pairwise
    {X : TopCat.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    {ι : Type u} [Fintype ι] (U : ι → Opens X) :
    PreservesLimit (Pairwise.diagram U).op
      ((pointwiseCocone (F ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X)).pt ⋙
        forget AddCommGrpCat.{u}) := by
  classical
  let G := F ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X
  let _ (i : I) : PreservesLimit (Pairwise.diagram U).op (G.obj i) :=
    TopCat.Presheaf.IsSheaf.isSheafPreservesLimitPairwiseIntersections U (F.obj i).property
  let : PreservesLimit (Pairwise.diagram U).op G.flip :=
    preservesLimit_of_evaluation G.flip (Pairwise.diagram U).op fun i ↦ by
      change PreservesLimit (Pairwise.diagram U).op (G.obj i)
      infer_instance
  change PreservesLimit (Pairwise.diagram U).op ((G.flip ⋙ colim) ⋙ forget AddCommGrpCat.{u})
  infer_instance

/-- Finite compatible families glue uniquely in the actual pointwise filtered colimit. -/
private theorem pointwise_filtered_colimit_finite_gluing
    {X : TopCat.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    let P := (pointwiseCocone (F ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X)).pt ⋙
      forget AddCommGrpCat.{u}
    ∀ ⦃ι : Type u⦄ [Fintype ι] (U : ι → Opens X) (sf : ∀ i, P.obj (op (U i))),
      TopCat.Presheaf.IsCompatible P U sf →
        ∃! s : P.obj (op (iSup U)), TopCat.Presheaf.IsGluing P U sf s := by
  dsimp only
  intro ι inst U sf hsf
  let P := (pointwiseCocone (F ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X)).pt ⋙
    forget AddCommGrpCat.{u}
  let : PreservesLimit (Pairwise.diagram U).op P :=
    pointwise_filtered_colimit_preserves_pairwise F U
  have h := isLimitOfPreserves P (Pairwise.coconeIsColimit U).op
  simpa only [P, Functor.mapCone, Cone.functoriality, Cocone.op, Pairwise.cocone,
    TopCat.Presheaf.isGluing_iff_pairwise, TopCat.Presheaf.IsCompatible.sectionPairwise] using
    (Types.isLimit_iff (P.mapCone (Pairwise.cocone U).op)).mp ⟨h⟩ _ hsf.sectionPairwise.prop

/-- The actual pointwise filtered colimit is a sheaf on a Noetherian space. -/
private theorem noetherian_pointwise_filtered_colimit_isSheaf
    {X : TopCat.{u}} [NoetherianSpace X] {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (pointwiseCocone (F ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X)).pt := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat.{u}) _).mpr
  exact noetherian_isSheaf_of_finite_gluing _ (pointwise_filtered_colimit_finite_gluing F)

/-- Filtered colimits of abelian sheaves on a Noetherian space are preserved in presheaves. -/
theorem noetherianSheaf_preservesFilteredColimits
    (X : TopCat.{u}) [NoetherianSpace X] (I : Type u) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (TopCat.Sheaf.forget AddCommGrpCat.{u} X) := by
  constructor
  intro F
  let : CreatesColimit F (TopCat.Sheaf.forget AddCommGrpCat.{u} X) :=
    CategoryTheory.Sheaf.createsColimitOfIsSheaf F fun c hc ↦ by
      let e : c.pt ≅ (pointwiseCocone (F ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X)).pt :=
        hc.coconePointUniqueUpToIso (pointwiseIsColimit _)
      rw [Presheaf.isSheaf_of_iso_iff e]
      exact noetherian_pointwise_filtered_colimit_isSheaf F
  infer_instance

/-- The canonical comparison is natural both in the diagram and as a presheaf. -/
noncomputable def noetherianFilteredColimitIso
    (X : TopCat.{u}) [NoetherianSpace X] (I : Type u) [SmallCategory I] [IsFiltered I] :
    (Functor.whiskeringRight I (TopCat.Sheaf AddCommGrpCat.{u} X)
        (TopCat.Presheaf AddCommGrpCat.{u} X)).obj
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X) ⋙ colim ≅
      colim ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X := by
  let := noetherianSheaf_preservesFilteredColimits X I
  exact (preservesColimitNatIso (TopCat.Sheaf.forget AddCommGrpCat.{u} X)).symm

/-- The canonical sectionwise comparison is an isomorphism for every open. -/
theorem noetherianFilteredColimit_sections_isIso
    (X : TopCat.{u}) [NoetherianSpace X] {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    IsIso (colimit.post F (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))) := by
  let : PreservesColimitsOfShape I (TopCat.Sheaf.forget AddCommGrpCat.{u} X) :=
    noetherianSheaf_preservesFilteredColimits X I
  let : PreservesColimitsOfShape I
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) := inferInstance
  let : PreservesColimitsOfShape I (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) := inferInstance
  infer_instance

/-- Hartshorne III.2, Lemma 2.8: a filtered colimit of flasque abelian sheaves on a
Noetherian space is flasque. -/
theorem filteredColimit_isFlasque
    (X : TopCat.{u}) [hX : NoetherianSpace X] {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) (hF : ∀ i, (F.obj i).IsFlasque) :
    (colimit F).IsFlasque := by
  let G := F ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X
  let e : G.flip ⋙ colim ≅ (colimit F).obj :=
    (colimitIsoFlipCompColim G).symm ≪≫ (noetherianFilteredColimitIso X I).app F
  let _ (i : I) : (F.obj i).IsFlasque := hF i
  refine ⟨?_⟩
  intro U V r
  let _ (i : I) : Epi ((G.flip.map r).app i) := by
    change Epi ((F.obj i).obj.map r)
    infer_instance
  have : Epi ((G.flip ⋙ colim).map r) := by
    change Epi (colimMap (G.flip.map r))
    infer_instance
  have : Epi (e.hom.app U ≫ (colimit F).obj.map r) := by
    rw [← e.hom.naturality r]
    infer_instance
  exact epi_of_epi (e.hom.app U) ((colimit F).obj.map r)

end Hartshorne
