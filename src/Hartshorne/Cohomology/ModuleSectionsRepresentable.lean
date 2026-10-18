/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Topology.Sheaves.Over
import Hartshorne.Scheme.OpenExtensionByZero

/-!
# Representing sections of module sheaves

For a ringed space (X, R) and an open U, the source object O_U is obtained by
module sheafification of the conditional presheaf R(V) for V ⊆ U and zero otherwise.
Its module actions and restrictions are inherited from R. For V ⊆ U, the image of
j⁻¹V is V itself, so the canonical ring restriction R(V) → R(V ∩ U) identifies this
presheaf with the proved ordinary abelian extension-by-zero construction.

The canonical generator is the image of the local unit 1 over U under the
module-sheafification unit; it is not a global unit over X. The free-Yoneda comparison
and the sheafification adjunction prove that evaluation at this generator gives an
additive equivalence. Its naturality is packaged as an isomorphism of Ab-valued
functors. The canonical maps O_V → O_U are monomorphisms, and their evaluation square
is exactly restriction of sections. No injectivity or flasqueness is assumed or proved here.

Mathlib's RingCat permits noncommutative rings. These arguments use only left-module
axioms, so that genuine generality includes the source's commutative ringed spaces.
The source is Hartshorne III.2, proof of Lemma 2.4, printed p. 207.
-/

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne

universe u

variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)

/-- The full rank-one module on opens contained in U, and the zero submodule otherwise. -/
private def conditionalSections (V : Opens X) :
    _root_.Submodule (R.obj.obj (op V)) ((PresheafOfModules.unit R.obj).obj (op V)) where
  carrier := {s | V ≤ U ∨ s = 0}
  zero_mem' := Or.inr rfl
  add_mem' := by
    intro a b ha hb
    rcases ha with h | ha
    · exact Or.inl h
    rcases hb with h | hb
    · exact Or.inl h
    exact Or.inr (by simp [ha, hb])
  smul_mem' := by
    intro a b hb
    rcases hb with h | hb
    · exact Or.inl h
    exact Or.inr (by simp [hb])

/-- The conditional rank-one submodules are stable under the ring's restriction maps. -/
private def conditionalSubmodule : (PresheafOfModules.unit R.obj).Submodule where
  obj V := conditionalSections R U V.unop
  map {V W} f := by
    intro s hs
    change W.unop ≤ U ∨ (PresheafOfModules.unit R.obj).map f s = 0
    rcases hs with h | hs
    · exact Or.inl ((leOfHom f.unop).trans h)
    right
    rw [hs, map_zero]

/-- The literal source presheaf: R(V) for V contained in U, and zero otherwise. -/
noncomputable def openStructureModulePresheaf : PresheafOfModules.{u} R.obj :=
  (conditionalSubmodule R U).toPresheafOfModules

/-- The canonical Yoneda seed sends an inclusion V → U to its local unit. -/
private def conditionalSeed :
    yoneda.obj U ⟶ (openStructureModulePresheaf R U).presheaf ⋙ forget Ab where
  app V := ↾fun i ↦ ⟨(1 : R.obj.obj V), Or.inl (leOfHom i)⟩
  naturality V W f := by
    apply ConcreteCategory.hom_ext
    intro i
    apply Subtype.ext
    change (1 : R.obj.obj W) = R.obj.map f (1 : R.obj.obj V)
    exact ((R.obj.map f).hom.map_one).symm

/-- The canonical free-Yoneda morphism, induced by the local-unit seed. -/
private noncomputable def freeComparison :
    (PresheafOfModules.free R.obj).obj (yoneda.obj U) ⟶ openStructureModulePresheaf R U :=
  PresheafOfModules.freeObjDesc (conditionalSeed R U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma freeComparison_app_freeMk (V : Opens X) (i : V ⟶ U) :
    (freeComparison R U).app (op V) (ModuleCat.freeMk i) =
      ⟨(1 : R.obj.obj (op V)), Or.inl (leOfHom i)⟩ := by
  change (ModuleCat.freeDesc ((conditionalSeed R U).app (op V))) (ModuleCat.freeMk i) = _
  exact ModuleCat.freeDesc_apply ((conditionalSeed R U).app (op V)) i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma freeComparison_val_eq (V : Opens X) (i : V ⟶ U)
    (s : (V ⟶ U) →₀ R.obj.obj (op V)) :
    ((freeComparison R U).app (op V) s).val = s i := by
  let : Subsingleton ((yoneda.obj U).obj (op V)) :=
    inferInstanceAs (Subsingleton (V ⟶ U))
  have h : (freeComparison R U).app (op V) ≫
      (conditionalSubmodule R U).ι.app (op V) =
        ModuleCat.ofHom
          (Finsupp.uniqueLinearEquiv (R.obj.obj (op V)) (R.obj.obj (op V)) i).toLinearMap := by
    apply ModuleCat.free_hom_ext
    intro j
    have hj : j = i := Subsingleton.elim _ _
    subst j
    change ((freeComparison R U).app (op V) (ModuleCat.freeMk i)).val = _
    rw [freeComparison_app_freeMk]
    change (1 : R.obj.obj (op V)) = (Finsupp.single i (1 : R.obj.obj (op V))) i
    simp
  have hs := ConcreteCategory.congr_hom h s
  change ((freeComparison R U).app (op V) s).val = s i at hs
  exact hs

private lemma freeComparison_app_bijective (V : Opens X) :
    Function.Bijective ((freeComparison R U).app (op V)) := by
  constructor
  · intro s t h
    apply Finsupp.ext
    intro i
    rw [← freeComparison_val_eq R U V i s, ← freeComparison_val_eq R U V i t]
    exact congrArg Subtype.val h
  · intro s
    rcases s.property with h | hs
    · refine ⟨Finsupp.single (homOfLE h) s.val, ?_⟩
      apply Subtype.ext
      rw [freeComparison_val_eq R U V (homOfLE h)]
      exact Finsupp.single_eq_same
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      change (((freeComparison R U).app (op V)).hom 0).val = s.val
      rw [map_zero]
      exact hs.symm

/-- The canonical free-Yoneda comparison is an isomorphism on the thin category of opens. -/
private noncomputable def freeComparisonIso :
    (PresheafOfModules.free R.obj).obj (yoneda.obj U) ≅ openStructureModulePresheaf R U := by
  let : Mono (freeComparison R U) :=
    PresheafOfModules.mono_of_injective fun V ↦ (freeComparison_app_bijective R U V.unop).1
  let : Epi (freeComparison R U) :=
    PresheafOfModules.epi_of_surjective fun V ↦ (freeComparison_app_bijective R U V.unop).2
  let : IsIso (freeComparison R U) := isIso_of_mono_of_epi (freeComparison R U)
  exact asIso (freeComparison R U)

/-- The underlying additive structure sheaf restricted to the open subspace U. -/
noncomputable def restrictedStructureAbelianSheaf : (TopCat.of U).Sheaf AddCommGrpCat.{u} :=
  (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj
    ((SheafOfModules.toSheaf.{u} R).obj (SheafOfModules.unit R))

/-- Natural ring restriction from V to the image of its inverse-image open V ∩ U. -/
private noncomputable def unitRestriction :
    (PresheafOfModules.unit R.obj).presheaf ⟶
      (Opens.map U.inclusion').op ⋙ U.isOpenEmbedding.functor.op ⋙
        (PresheafOfModules.unit R.obj).presheaf :=
  Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit)
    (PresheafOfModules.unit R.obj).presheaf

private lemma unitRestriction_bijective (V : Opens X) (h : V ≤ U) :
    Function.Bijective ((unitRestriction R U).app (op V)) := by
  have hobj : (Opens.map U.inclusion' ⋙ U.isOpenEmbedding.functor).obj V = V := by
    simp only [Functor.comp_obj, Opens.functor_map_eq_inf, inf_eq_left.mpr h]
  have hc : U.isOpenEmbedding.isOpenMap.adjunction.counit.app V = eqToHom hobj :=
    Subsingleton.elim _ _
  let : IsIso (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V) := by
    rw [hc]
    infer_instance
  change Function.Bijective ((PresheafOfModules.unit R.obj).presheaf.map
    (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op)
  exact ConcreteCategory.bijective_of_isIso _

/-- The canonical restriction map to the proved ordinary abelian conditional presheaf. -/
private noncomputable def ordinaryRawComparison :
    (openStructureModulePresheaf R U).presheaf ⟶
      Hartshorne.openExtensionByZeroPresheaf U (restrictedStructureAbelianSheaf R U) where
  app V := AddCommGrpCat.ofHom
    { toFun := fun s ↦ ⟨((unitRestriction R U).app V).hom s.val, by
        rcases s.property with h | hs
        · exact Or.inl h
        · right
          change ((unitRestriction R U).app V).hom s.val = 0
          rw [hs]
          exact map_zero ((unitRestriction R U).app V).hom⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero ((unitRestriction R U).app V).hom
      map_add' := by
        intro s t
        apply Subtype.ext
        exact map_add ((unitRestriction R U).app V).hom s.val t.val }
  naturality V W f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((unitRestriction R U).naturality f) s.val

private lemma ordinaryRawComparison_app_bijective (V : Opens X) :
    Function.Bijective ((ordinaryRawComparison R U).app (op V)) := by
  by_cases h : V ≤ U
  · obtain ⟨hi, hs⟩ := unitRestriction_bijective R U V h
    constructor
    · intro s t hst
      apply Subtype.ext
      exact hi (congrArg Subtype.val hst)
    · intro s
      obtain ⟨t, ht⟩ := hs s.val
      exact ⟨⟨t, Or.inl h⟩, Subtype.ext ht⟩
  · let : Subsingleton ((openStructureModulePresheaf R U).presheaf.obj (op V)) :=
      ⟨fun s t ↦ Subtype.ext ((s.property.resolve_left h).trans
        (t.property.resolve_left h).symm)⟩
    constructor
    · exact Function.injective_of_subsingleton _
    · intro s
      refine ⟨0, ?_⟩
      apply Subtype.ext
      change ((unitRestriction R U).app (op V)).hom 0 = s.val
      rw [map_zero]
      exact (s.property.resolve_left h).symm

/-- The raw comparison is invertible: restriction is identity inside U, and zero outside. -/
private noncomputable def ordinaryRawComparisonIso :
    (openStructureModulePresheaf R U).presheaf ≅
      Hartshorne.openExtensionByZeroPresheaf U (restrictedStructureAbelianSheaf R U) := by
  let : IsIso (ordinaryRawComparison R U) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (ordinaryRawComparison_app_bijective R U V.unop)
  exact asIso (ordinaryRawComparison R U)

/-- Hartshorne's O_U: module sheafification of the literal conditional structure presheaf. -/
noncomputable def openStructureModule : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj (openStructureModulePresheaf R U)

/-- The underlying sheaf of O_U is canonically ordinary extension by zero of R restricted to U. -/
noncomputable def openStructureModuleUnderlyingIso :
    (SheafOfModules.toSheaf.{u} R).obj (openStructureModule R U) ≅
      Hartshorne.openExtensionByZero U (restrictedStructureAbelianSheaf R U) :=
  (PresheafOfModules.sheafificationCompToSheaf.{u} (𝟙 R.obj)).app
      (openStructureModulePresheaf R U) ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso
      (ordinaryRawComparisonIso R U)

/-- Precomposition with the canonical free-Yoneda comparison is additive. -/
private noncomputable def conditionalHomAddEquiv (M : PresheafOfModules.{u} R.obj) :
    (openStructureModulePresheaf R U ⟶ M) ≃+
      ((PresheafOfModules.free R.obj).obj (yoneda.obj U) ⟶ M) :=
  { (freeComparisonIso R U).symm.homCongr (Iso.refl M) with
    map_add' := by
      intro f g
      simp [Iso.homCongr, Preadditive.comp_add] }

/-- The free-Yoneda section equivalence is additive, with evaluation at its identity generator. -/
private noncomputable def freeSectionAddEquiv (M : PresheafOfModules.{u} R.obj) :
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U) ⟶ M) ≃+ M.obj (op U) :=
  { PresheafOfModules.freeYonedaEquiv (M := M) (X := U) with
    map_add' := by intro f g; rfl }

/-- The local unit of O_U, obtained by applying the module-sheafification unit to 1 over U. -/
noncomputable def openStructureModuleGenerator : (openStructureModule R U).val.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
    (openStructureModulePresheaf R U)).app (op U)
      ⟨(1 : R.obj.obj (op U)), Or.inl le_rfl⟩

/-- Evaluation at the local unit of O_U gives the canonical additive section equivalence. -/
noncomputable def moduleSectionsAddEquiv (F : SheafOfModules.{u} R) :
    (openStructureModule R U ⟶ F) ≃+ F.val.obj (op U) := by
  let : (PresheafOfModules.sheafification.{u} (𝟙 R.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).left_adjoint_additive
  exact (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homAddEquiv
    (openStructureModulePresheaf R U) F).trans (conditionalHomAddEquiv R U _)).trans
      (freeSectionAddEquiv R U _)

/-- The section equivalence is precisely evaluation at the sheafified local unit over U. -/
lemma moduleSectionsAddEquiv_apply (F : SheafOfModules.{u} R) (f : openStructureModule R U ⟶ F) :
    moduleSectionsAddEquiv R U F f = f.val.app (op U) (openStructureModuleGenerator R U) := by
  change PresheafOfModules.freeYonedaEquiv
    ((freeComparisonIso R U).hom ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
        (openStructureModulePresheaf R U) F f) = _
  rw [PresheafOfModules.freeYonedaEquiv_comp]
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
    (openStructureModulePresheaf R U) F f).app (op U)
      ((freeComparison R U).app (op U) (ModuleCat.freeMk (𝟙 U))) = _
  rw [freeComparison_app_freeMk R U U (𝟙 U)]
  rfl

/-- The canonical additive section equivalence is natural in the module sheaf. -/
lemma moduleSectionsAddEquiv_naturality (F G : SheafOfModules.{u} R)
    (f : openStructureModule R U ⟶ F) (φ : F ⟶ G) :
    moduleSectionsAddEquiv R U G (f ≫ φ) =
      φ.val.app (op U) (moduleSectionsAddEquiv R U F f) := by
  rw [moduleSectionsAddEquiv_apply, moduleSectionsAddEquiv_apply]
  rfl

/-- Hartshorne's natural additive isomorphism Hom(O_U, F) ≅ F(U). -/
noncomputable def moduleSectionsIso :
    preadditiveCoyoneda.obj (op (openStructureModule R U)) ≅
      SheafOfModules.evaluation.{u} R (op U) ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun F ↦ (moduleSectionsAddEquiv R U F).toAddCommGrpIso) (by
    intro F G φ
    apply ConcreteCategory.hom_ext
    intro f
    exact moduleSectionsAddEquiv_naturality R U F G f φ)

private lemma conditionalSubmodule_le (V : Opens X) (h : V ≤ U) :
    conditionalSubmodule R V ≤ conditionalSubmodule R U := by
  intro W s hs
  change W.unop ≤ U ∨ s = 0
  rcases hs with hW | hs
  · exact Or.inl (hW.trans h)
  · exact Or.inr hs

/-- The canonical morphism O_V → O_U for an inclusion V ⊆ U. -/
noncomputable def openStructureModuleInclusion (V : Opens X) (h : V ≤ U) :
    openStructureModule R V ⟶ openStructureModule R U :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    (PresheafOfModules.Submodule.homOfLE (conditionalSubmodule_le R U V h))

/-- The canonical open-inclusion morphism is mono, by left exactness of module sheafification. -/
instance openStructureModuleInclusion_mono (V : Opens X) (h : V ≤ U) :
    Mono (openStructureModuleInclusion R U V h) := by
  let F : PresheafOfModules.{u} R.obj ⥤ SheafOfModules.{u} R :=
    PresheafOfModules.sheafification (𝟙 R.obj)
  let i : openStructureModulePresheaf R V ⟶ openStructureModulePresheaf R U :=
    PresheafOfModules.Submodule.homOfLE (conditionalSubmodule_le R U V h)
  let : Mono i := PresheafOfModules.Submodule.instMonoHomOfLE
    (conditionalSubmodule R V) (conditionalSubmodule R U) (conditionalSubmodule_le R U V h)
  let : CategoryTheory.Limits.PreservesFiniteLimits F := inferInstance
  exact preserves_mono_of_preservesLimit F i

/-- The included local unit over V is the restriction of the local unit over U. -/
lemma openStructureModuleInclusion_generator (V : Opens X) (h : V ≤ U) :
    (openStructureModuleInclusion R U V h).val.app (op V) (openStructureModuleGenerator R V) =
      (openStructureModule R U).val.map (homOfLE h).op (openStructureModuleGenerator R U) := by
  let i : openStructureModulePresheaf R V ⟶ openStructureModulePresheaf R U :=
    PresheafOfModules.Submodule.homOfLE (conditionalSubmodule_le R U V h)
  let oneV : (openStructureModulePresheaf R V).obj (op V) :=
    ⟨(1 : R.obj.obj (op V)), Or.inl le_rfl⟩
  let oneU : (openStructureModulePresheaf R U).obj (op U) :=
    ⟨(1 : R.obj.obj (op U)), Or.inl le_rfl⟩
  let g : op U ⟶ op V := (homOfLE h).op
  let ηU : openStructureModulePresheaf R U ⟶
      (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj (openStructureModule R U).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
      (openStructureModulePresheaf R U)
  have hone : i.app (op V) oneV = (openStructureModulePresheaf R U).map g oneU := by
    apply Subtype.ext
    change (1 : R.obj.obj (op V)) = R.obj.map g (1 : R.obj.obj (op U))
    exact ((R.obj.map g).hom.map_one).symm
  have hunit := congrArg
    (fun f : openStructureModulePresheaf R V ⟶
      (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj (openStructureModule R U).val ↦
        f.app (op V) oneV)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.naturality i)
  have h₁ :
      (openStructureModuleInclusion R U V h).val.app (op V) (openStructureModuleGenerator R V) =
      ηU.app (op V) (i.app (op V) oneV) := hunit.symm
  have h₂ : ηU.app (op V) (i.app (op V) oneV) =
      ηU.app (op V) ((openStructureModulePresheaf R U).map g oneU) :=
    congrArg (ηU.app (op V)) hone
  have h₃ : ηU.app (op V) ((openStructureModulePresheaf R U).map g oneU) =
      (openStructureModule R U).val.map g (openStructureModuleGenerator R U) :=
    PresheafOfModules.naturality_apply ηU g oneU
  exact h₁.trans (h₂.trans h₃)

/-- Canonical evaluation carries precomposition by O_V → O_U to restriction of sections. -/
lemma moduleSectionsAddEquiv_restriction (F : SheafOfModules.{u} R)
    (V : Opens X) (h : V ≤ U) (f : openStructureModule R U ⟶ F) :
    moduleSectionsAddEquiv R V F (openStructureModuleInclusion R U V h ≫ f) =
      F.val.map (homOfLE h).op (moduleSectionsAddEquiv R U F f) := by
  rw [moduleSectionsAddEquiv_apply, moduleSectionsAddEquiv_apply]
  change f.val.app (op V)
    ((openStructureModuleInclusion R U V h).val.app (op V) (openStructureModuleGenerator R V)) = _
  rw [openStructureModuleInclusion_generator]
  exact PresheafOfModules.naturality_apply f.val (homOfLE h).op (openStructureModuleGenerator R U)

end Hartshorne
