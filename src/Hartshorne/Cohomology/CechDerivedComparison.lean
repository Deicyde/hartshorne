/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.CechZeroGlobalSections
import Hartshorne.Cohomology.ResolutionToInjectiveComparison
import Hartshorne.Cohomology.SheafCohomology
import Hartshorne.Cohomology.SheafifiedCechResolution

/-!
# The comparison map from Čech to sheaf cohomology

Hartshorne, *Algebraic Geometry*, III, Lemma 4.4 (p. 221).

For an open cover `U` of a topological space `X`, the augmentation `F → 𝒞^•(U, F)` is a
resolution of `F` (Lemma 4.2). Comparing it with the chosen injective resolution of `F` gives a
cochain map, unique up to homotopy, and applying the global section functor and taking
cohomology gives the natural map `Ȟ^p(U, F) → H^p(X, F)`, written
`Hartshorne.cechToSheafCohomology U hU p`. In degree zero it is compatible with the
identifications of both sides with global sections
(`Hartshorne.cechToSheafCohomology_zero_comp`), hence an isomorphism.

Naturality in `F` uses that two cochain maps from a resolution to a complex of injectives
which agree after the augmentation are homotopic
(`Hartshorne.CechDerivedComparison.homotopyOfComp`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hartshorne

universe u

namespace CechDerivedComparison

section Homotopy

open HomologicalComplex CochainComplex

variable {C : Type*} [Category C] [Abelian C]
  {A : C} {K : CochainComplex C ℕ}
  (epsilon : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso epsilon]

include epsilon

private lemma exactAt_succ (n : ℕ) : K.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt epsilon (n + 1)
    (CochainComplex.exactAt_succ_single_obj A n)]
  infer_instance

private lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (K.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (exactAt_succ epsilon n)

private lemma exact_succ_succ (n : ℕ) :
    (ShortComplex.mk _ _ (K.d_comp_d (n + 1) (n + 2) (n + 3))).Exact := by
  simpa only [Nat.add_assoc, Nat.reduceAdd] using exact_succ epsilon (n + 1)

omit [QuasiIso epsilon] in
@[reassoc]
private lemma epsilon_f_zero_comp_d : epsilon.f 0 ≫ K.d 0 1 = 0 := by
  rw [HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d, zero_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def isLimitKernelFork :
    IsLimit (KernelFork.ofι (Z := A) (epsilon.f 0) (epsilon_f_zero_comp_d epsilon)) := by
  refine IsLimit.ofIsoLimit (K.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 A).symm ≪≫
    isoOfQuasiIsoAt epsilon 0 ≪≫
    K.isoHomologyπ₀.symm) ?_
  simp [singleObjHomologySelfIso, singleObjCyclesSelfIso]

private lemma exact_zero :
    (ShortComplex.mk _ _ (epsilon_f_zero_comp_d epsilon)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelFork epsilon)

variable {L : CochainComplex C ℕ} [∀ n, Injective (L.X n)]

private def homotopyZeroZero (f : K ⟶ L) (comm : epsilon ≫ f = 0) : K.X 1 ⟶ L.X 0 :=
  (exact_zero epsilon).descToInjective (f.f 0)
    (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
private lemma comp_homotopyZeroZero (f : K ⟶ L) (comm : epsilon ≫ f = 0) :
    K.d 0 1 ≫ homotopyZeroZero epsilon f comm = f.f 0 :=
  (exact_zero epsilon).comp_descToInjective _ _

private def homotopyZeroOne (f : K ⟶ L) (comm : epsilon ≫ f = 0) : K.X 2 ⟶ L.X 1 :=
  (exact_succ epsilon 0).descToInjective
    (f.f 1 - homotopyZeroZero epsilon f comm ≫ L.d 0 1)
    (by rw [Preadditive.comp_sub, comp_homotopyZeroZero_assoc epsilon f comm,
      HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
private lemma comp_homotopyZeroOne (f : K ⟶ L) (comm : epsilon ≫ f = 0) :
    K.d 1 2 ≫ homotopyZeroOne epsilon f comm =
      f.f 1 - homotopyZeroZero epsilon f comm ≫ L.d 0 1 :=
  (exact_succ epsilon 0).comp_descToInjective _ _

private def homotopyZeroSucc (f : K ⟶ L) (n : ℕ)
    (g : K.X (n + 1) ⟶ L.X n) (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : f.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.X (n + 3) ⟶ L.X (n + 2) :=
  (exact_succ_succ epsilon n).descToInjective
    (f.f (n + 2) - g' ≫ L.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w,
        Preadditive.add_comp, Category.assoc, Category.assoc,
        L.d_comp_d, comp_zero, add_zero, sub_self])

@[reassoc (attr := simp)]
private lemma comp_homotopyZeroSucc (f : K ⟶ L) (n : ℕ)
    (g : K.X (n + 1) ⟶ L.X n) (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : f.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.d (n + 2) (n + 3) ≫ homotopyZeroSucc epsilon f n g g' w =
      f.f (n + 2) - g' ≫ L.d _ _ :=
  (exact_succ_succ epsilon n).comp_descToInjective _ _

private def homotopyZero (f : K ⟶ L) (comm : epsilon ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroZero epsilon f comm) (by simp)
    (homotopyZeroOne epsilon f comm) (by simp)
    (fun n ⟨g, g', w⟩ ↦
      ⟨homotopyZeroSucc epsilon f n g g' (by simp only [w, add_comm]), by simp⟩)

/-- Two cochain maps from a resolution `epsilon : A → K` to a complex of injective objects which
agree after composing with the augmentation are cochain-homotopic. -/
def homotopyOfComp (f g : K ⟶ L) (h : epsilon ≫ f = epsilon ≫ g) : Homotopy f g :=
  Homotopy.equivSubZero.invFun
    (homotopyZero epsilon _ (by rw [Preadditive.comp_sub, h, sub_self]))

end Homotopy

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]

/-- `Γ(X, 𝒞^•(U, F)) ≅ C^•(U, F)`, stated with the global section functor used to define sheaf
cohomology. -/
def globalSectionsIso (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (SheafifiedCech.sheafifiedCechComplex U F) ≅ orderedCechComplex U F :=
  SheafifiedCech.globalSectionsIso U F

theorem globalSectionsIso_inv_naturality (U : ι → Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) :
    orderedCechComplexMap U f ≫ (globalSectionsIso U G).inv =
      (globalSectionsIso U F).inv ≫
        ((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SheafifiedCech.sheafifiedCechComplexMap U f) :=
  (SheafifiedCech.globalSectionsNatIso U).inv.naturality f

/-- The chosen comparison cochain map from the sheafified Čech resolution `𝒞^•(U, F)` to the
chosen injective resolution of `F`, commuting with the augmentations. -/
def comparisonHom (U : ι → Opens X) (hU : IsOpenCover U) (F : X.Sheaf AddCommGrpCat.{u}) :
    SheafifiedCech.sheafifiedCechComplex U F ⟶ (injectiveResolution F).cocomplex :=
  haveI := SheafifiedCech.quasiIso_augmentationHom U hU F
  ResolutionToInjectiveComparison.hom (SheafifiedCech.augmentationHom U F)
    (injectiveResolution F)

@[reassoc (attr := simp)]
theorem augmentationHom_comp_comparisonHom (U : ι → Opens X) (hU : IsOpenCover U)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    SheafifiedCech.augmentationHom U F ≫ comparisonHom U hU F = (injectiveResolution F).ι :=
  haveI := SheafifiedCech.quasiIso_augmentationHom U hU F
  ResolutionToInjectiveComparison.commutes _ _

/-- The cochain map `C^•(U, F) ≅ Γ(X, 𝒞^•(U, F)) → Γ(X, I^•)` to global sections of the chosen
injective resolution `I^•` of `F`. -/
def globalSectionsComparison (U : ι → Opens X) (hU : IsOpenCover U)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    orderedCechComplex U F ⟶ ((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex :=
  (globalSectionsIso U F).inv ≫
    ((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (comparisonHom U hU F)

/-- `H^p(X, F)` computed from global sections of the chosen injective resolution of `F`. -/
def sheafCohomologyIso (X : TopCat.{u}) (p : ℕ) (F : X.Sheaf AddCommGrpCat.{u}) :
    (sheafCohomology X p).obj F ≅ (((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).homology p :=
  (injectiveResolution F).isoRightDerivedObj (sheafSectionsOver (X := X) ⊤) p

/-- The component at `F` of the comparison map `Ȟ^p(U, F) → H^p(X, F)`. -/
def cechToSheafCohomologyApp (U : ι → Opens X) (hU : IsOpenCover U) (p : ℕ)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    (orderedCechCohomologyFunctor U p).obj F ⟶ (sheafCohomology X p).obj F :=
  HomologicalComplex.homologyMap (globalSectionsComparison U hU F) p ≫
    (sheafCohomologyIso X p F).inv

theorem cechToSheafCohomologyApp_naturality (U : ι → Opens X) (hU : IsOpenCover U) (p : ℕ)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    (orderedCechCohomologyFunctor U p).map f ≫ cechToSheafCohomologyApp U hU p G =
      cechToSheafCohomologyApp U hU p F ≫ (sheafCohomology X p).map f := by
  let φ := InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)
  have key : Homotopy (SheafifiedCech.sheafifiedCechComplexMap U f ≫ comparisonHom U hU G)
      (comparisonHom U hU F ≫ φ) := by
    haveI := SheafifiedCech.quasiIso_augmentationHom U hU F
    refine homotopyOfComp (SheafifiedCech.augmentationHom U F) _ _ ?_
    have hnat := (SheafifiedCech.augmentationNatTrans U).naturality f
    change (CochainComplex.single₀ _).map f ≫ SheafifiedCech.augmentationHom U G =
      SheafifiedCech.augmentationHom U F ≫ SheafifiedCech.sheafifiedCechComplexMap U f at hnat
    rw [← Category.assoc, ← hnat, Category.assoc, augmentationHom_comp_comparisonHom,
      augmentationHom_comp_comparisonHom_assoc, InjectiveResolution.desc_commutes]
  have e2 := ((sheafSectionsOver (X := X) ⊤).mapHomotopy key).homologyMap_eq p
  have e3 : (sheafCohomologyIso X p F).inv ≫ ((sheafSectionsOver (X := X) ⊤).rightDerived p).map f =
      HomologicalComplex.homologyMap
        (((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) p ≫
          (sheafCohomologyIso X p G).inv :=
    InjectiveResolution.isoRightDerivedObj_inv_naturality f (injectiveResolution F)
      (injectiveResolution G) φ (InjectiveResolution.desc_commutes_zero _ _ _)
      (sheafSectionsOver (X := X) ⊤) p
  have main : HomologicalComplex.homologyMap (orderedCechComplexMap U f) p ≫
      HomologicalComplex.homologyMap (globalSectionsComparison U hU G) p ≫
        (sheafCohomologyIso X p G).inv =
      (HomologicalComplex.homologyMap (globalSectionsComparison U hU F) p ≫
        (sheafCohomologyIso X p F).inv) ≫
          ((sheafSectionsOver (X := X) ⊤).rightDerived p).map f := by
    rw [Category.assoc, e3, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [← HomologicalComplex.homologyMap_comp, globalSectionsComparison]
    rw [← Category.assoc, globalSectionsIso_inv_naturality, Category.assoc, Category.assoc,
      ← Functor.map_comp, HomologicalComplex.homologyMap_comp, e2,
      ← HomologicalComplex.homologyMap_comp, Functor.map_comp]
  exact main

/-- **Hartshorne III, Lemma 4.4.** For an open cover `U` of `X` and every degree `p`, the
natural map `Ȟ^p(U, F) → H^p(X, F)` from ordered Čech cohomology to sheaf cohomology, natural in
the abelian sheaf `F`. It is induced on global sections by a comparison cochain map from the
sheafified Čech resolution `F → 𝒞^•(U, F)` to an injective resolution of `F`. -/
def _root_.Hartshorne.cechToSheafCohomology (U : ι → Opens X) (hU : IsOpenCover U) (p : ℕ) :
    orderedCechCohomologyFunctor U p ⟶ sheafCohomology X p where
  app F := cechToSheafCohomologyApp U hU p F
  naturality _ _ f := cechToSheafCohomologyApp_naturality U hU p f

theorem sectionsFunctorIsoOfEq_hom_app {V W : Opens X} (h : V = W)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    (CechZero.sectionsFunctorIsoOfEq h).hom.app F = F.presheaf.map (homOfLE h.ge).op := by
  subst h
  exact (F.presheaf.map_id _).symm

/-- `Ȟ^0(U, F) ≅ Γ(X, F)`, with the source written as the homology of the Čech complex. -/
def cechH0Iso (U : ι → Opens X) (hU : IsOpenCover U) (F : X.Sheaf AddCommGrpCat.{u}) :
    (orderedCechComplex U F).homology 0 ≅ (sheafSectionsOver (X := X) ⊤).obj F :=
  orderedCechH0IsoGlobalSections U F hU

/-- The gluing isomorphism `Ȟ^0(U, F) ≅ Γ(X, F)` sends the class of a degree-zero cocycle to the
section restricting to that cocycle on the members of the cover. -/
theorem cechH0Iso_restrict (U : ι → Opens X) (hU : IsOpenCover U)
    (F : X.Sheaf AddCommGrpCat.{u}) (x : (orderedCechComplex U F).cycles 0)
    (a : OrderedCechIndex ι 0) :
    F.presheaf.map (homOfLE (le_top : orderedCechIntersection U a ≤ ⊤)).op
        ((cechH0Iso U hU F).hom ((orderedCechComplex U F).homologyπ 0 x)) =
      (orderedCechComplex U F).iCycles 0 x a := by
  let h := (CechZero.homologyData U F).left
  have h3 : h.homologyIso.hom (((orderedCechComplex U F).sc 0).homologyπ x) =
      h.cyclesIso.hom x :=
    ConcreteCategory.congr_hom h.homologyπ_comp_homologyIso_hom x
  have h2 : (h.cyclesIso.hom x).1 = (orderedCechComplex U F).iCycles 0 x :=
    ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i x
  change F.presheaf.map _ ((CechZero.sectionsFunctorIsoOfEq
    ((CechZero.iSup_opens U).trans hU.iSup_eq_top)).hom.app F
      (CechZero.glue U F (h.homologyIso.hom (((orderedCechComplex U F).sc 0).homologyπ x)))) = _
  rw [h3, sectionsFunctorIsoOfEq_hom_app, ← h2]
  exact (SheafifiedCech.map_map F _ _ _).trans
    (CechZero.glue_restrict U F (h.cyclesIso.hom x) a)

set_option backward.isDefEq.respectTransparency false in
theorem iCycles_comp_globalSectionsComparison_f_zero (U : ι → Opens X) (hU : IsOpenCover U)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    (orderedCechComplex U F).iCycles 0 ≫ (globalSectionsComparison U hU F).f 0 =
      (orderedCechComplex U F).homologyπ 0 ≫ (cechH0Iso U hU F).hom ≫
        (sheafSectionsOver (X := X) ⊤).map ((injectiveResolution F).ι.f 0) := by
  have k1 : (sheafSectionsOver (X := X) ⊤).map ((injectiveResolution F).ι.f 0) =
      (sheafSectionsOver (X := X) ⊤).map ((SheafifiedCech.augmentationHom U F).f 0) ≫
        (sheafSectionsOver (X := X) ⊤).map ((comparisonHom U hU F).f 0) := by
    rw [← Functor.map_comp, ← HomologicalComplex.comp_f, augmentationHom_comp_comparisonHom]
  have k2 : (orderedCechComplex U F).iCycles 0 ≫ (globalSectionsIso U F).inv.f 0 =
      (orderedCechComplex U F).homologyπ 0 ≫ (cechH0Iso U hU F).hom ≫
        (sheafSectionsOver (X := X) ⊤).map ((SheafifiedCech.augmentationHom U F).f 0) := by
    rw [← cancel_mono ((globalSectionsIso U F).hom.f 0), Category.assoc,
      ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f, Category.comp_id]
    ext x
    funext a
    rw [← cechH0Iso_restrict U hU F x a]
    exact (SheafifiedCech.map_map F _ _ _).symm
  rw [k1]
  change _ ≫ (globalSectionsIso U F).inv.f 0 ≫
    (sheafSectionsOver (X := X) ⊤).map ((comparisonHom U hU F).f 0) = _
  rw [← Category.assoc, k2]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_globalSectionsComparison_zero (U : ι → Opens X) (hU : IsOpenCover U)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    HomologicalComplex.homologyMap (globalSectionsComparison U hU F) 0 =
      (cechH0Iso U hU F).hom ≫
        (injectiveResolution F).toRightDerivedZero' (sheafSectionsOver (X := X) ⊤) ≫
          (CochainComplex.isoHomologyπ₀ _).hom := by
  have hcyc : HomologicalComplex.cyclesMap (globalSectionsComparison U hU F) 0 =
      (orderedCechComplex U F).homologyπ 0 ≫ (cechH0Iso U hU F).hom ≫
        (injectiveResolution F).toRightDerivedZero' (sheafSectionsOver (X := X) ⊤) := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0), HomologicalComplex.cyclesMap_i]
    refine (iCycles_comp_globalSectionsComparison_f_zero U hU F).trans ?_
    rw [← InjectiveResolution.toRightDerivedZero'_comp_iCycles, Category.assoc, Category.assoc]
  have hπ₀ : (CochainComplex.isoHomologyπ₀ (((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)).hom =
        HomologicalComplex.homologyπ _ 0 := rfl
  rw [← cancel_epi ((orderedCechComplex U F).homologyπ 0),
    HomologicalComplex.homologyπ_naturality, hcyc, hπ₀]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **Hartshorne III, Lemma 4.4, degree zero.** In degree zero, the comparison map
`Ȟ^0(U, F) → H^0(X, F)` followed by `H^0(X, F) ≅ Γ(X, F)` is the gluing isomorphism
`Ȟ^0(U, F) ≅ Γ(X, F)`. -/
theorem _root_.Hartshorne.cechToSheafCohomology_zero_comp (U : ι → Opens X)
    (hU : IsOpenCover U) (F : X.Sheaf AddCommGrpCat.{u}) :
    (cechToSheafCohomology U hU 0).app F ≫ (sheafCohomologyZeroIso X).hom.app F =
      (orderedCechH0IsoGlobalSections U F hU).hom := by
  have hinv : (sheafCohomologyZeroIso X).hom.app F ≫
      (sheafSectionsOver (X := X) ⊤).toRightDerivedZero.app F = 𝟙 _ := by
    rw [← NatTrans.comp_app]
    exact congrArg (fun α ↦ NatTrans.app α F)
      (sheafSectionsOver (X := X) ⊤).rightDerivedZeroIsoSelf_hom_inv_id
  have hT : (sheafSectionsOver (X := X) ⊤).toRightDerivedZero.app F =
      (injectiveResolution F).toRightDerivedZero' (sheafSectionsOver (X := X) ⊤) ≫
        (CochainComplex.isoHomologyπ₀ _).hom ≫ (sheafCohomologyIso X 0 F).inv :=
    (injectiveResolution F).toRightDerivedZero_eq (sheafSectionsOver (X := X) ⊤)
  have main : (HomologicalComplex.homologyMap (globalSectionsComparison U hU F) 0 ≫
      (sheafCohomologyIso X 0 F).inv) ≫ (sheafCohomologyZeroIso X).hom.app F =
        (cechH0Iso U hU F).hom := by
    rw [← cancel_mono ((sheafSectionsOver (X := X) ⊤).toRightDerivedZero.app F),
      Category.assoc, hinv, Category.comp_id, hT, homologyMap_globalSectionsComparison_zero]
    simp only [Category.assoc]
  exact main

/-- In degree zero the comparison map `Ȟ^0(U, -) → H^0(X, -)` is an isomorphism. -/
instance _root_.Hartshorne.isIso_cechToSheafCohomology_zero (U : ι → Opens X)
    (hU : IsOpenCover U) : IsIso (cechToSheafCohomology U hU 0) := by
  have (F : X.Sheaf AddCommGrpCat.{u}) : IsIso ((cechToSheafCohomology U hU 0).app F) := by
    have : IsIso ((cechToSheafCohomology U hU 0).app F ≫
        (sheafCohomologyZeroIso X).hom.app F) := by
      rw [cechToSheafCohomology_zero_comp]
      exact Iso.isIso_hom (orderedCechH0IsoGlobalSections U F hU)
    exact IsIso.of_isIso_comp_right _ ((sheafCohomologyZeroIso X).hom.app F)
  exact NatIso.isIso_of_isIso_app _

end CechDerivedComparison

end Hartshorne
