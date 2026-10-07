/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.OrderedCechComplex
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Zeroth ordered Cech cohomology

Hartshorne, *Algebraic Geometry*, III, Lemma 4.1 (p. 220).

For an open cover, the kernel of the first ordered Cech differential consists exactly of
compatible families of local sections. The sheaf gluing condition identifies these families with
global sections. Since the incoming differential in degree zero is zero, this identifies zeroth
Cech cohomology with global sections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopologicalSpace.Opens
open scoped BigOperators Matrix

namespace Hartshorne

universe u

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]

namespace CechZero

/-- The increasing singleton tuple corresponding to an index of the cover. -/
def singletonIndex (i : ι) : OrderedCechIndex ι 0 :=
  ⟨fun _ => i, by
    rw [Fin.strictMono_iff_lt_succ]
    exact fun q => Fin.elim0 q⟩

@[simp]
theorem singletonIndex_apply (i : ι) (q : Fin 1) :
    (singletonIndex i).1 q = i :=
  rfl

theorem singletonIndex_value (a : OrderedCechIndex ι 0) :
    singletonIndex (a.1 0) = a := by
  apply Subtype.ext
  funext q
  rw [Fin.eq_zero q]
  rfl

/-- The increasing pair associated to two strictly ordered cover indices. -/
def pairIndex (i j : ι) (h : i < j) : OrderedCechIndex ι 1 :=
  ⟨![i, j], by
    rw [Fin.strictMono_iff_lt_succ]
    intro q
    fin_cases q
    simpa using h⟩

@[simp]
theorem pairIndex_remove_zero (i j : ι) (h : i < j) :
    (pairIndex i j h).remove 0 = singletonIndex j := by
  apply Subtype.ext
  funext q
  fin_cases q
  rfl

@[simp]
theorem pairIndex_remove_one (i j : ι) (h : i < j) :
    (pairIndex i j h).remove 1 = singletonIndex i := by
  apply Subtype.ext
  funext q
  fin_cases q
  rfl

@[simp]
theorem intersection_singletonIndex (U : ι → Opens X) (i : ι) :
    orderedCechIntersection U (singletonIndex i) = U i := by
  rw [orderedCechIntersection]
  simp

@[simp]
theorem intersection_pairIndex (U : ι → Opens X) (i j : ι) (h : i < j) :
    orderedCechIntersection U (pairIndex i j h) = U i ⊓ U j := by
  apply le_antisymm
  · refine le_inf (iInf_le_of_le 0 ?_) (iInf_le_of_le 1 ?_) <;> rfl
  · refine le_iInf fun q => ?_
    fin_cases q <;> simp [pairIndex]

/-- The open family naturally indexing degree-zero ordered Cech cochains. -/
abbrev opens (U : ι → Opens X) (a : OrderedCechIndex ι 0) : Opens X :=
  orderedCechIntersection U a

theorem iSup_opens (U : ι → Opens X) :
    iSup (opens U) = iSup U := by
  apply le_antisymm
  · refine iSup_le fun a => ?_
    rw [← singletonIndex_value a, opens, intersection_singletonIndex]
    exact le_iSup U (a.1 0)
  · refine iSup_le fun i => ?_
    rw [← intersection_singletonIndex U i]
    exact le_iSup (opens U) (singletonIndex i)

/-- Evaluation of an abelian sheaf on a fixed open set. -/
def sectionsFunctor (V : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj F := F.presheaf.obj (op V)
  map f := f.hom.app (op V)
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem pair_le_remove (U : ι → Opens X) (a : OrderedCechIndex ι 1)
    (q : Fin 2) :
    orderedCechIntersection U a ≤ orderedCechIntersection U (a.remove q) := by
  rw [orderedCechIntersection, orderedCechIntersection]
  refine le_iInf fun j => ?_
  exact iInf_le_of_le (q.succAbove j) le_rfl

private theorem differential_zero_apply_pair (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) (s : orderedCechCochains U F 0)
    (i j : ι) (h : i < j) :
    orderedCechDifferential U F 0 s (pairIndex i j h) =
      F.presheaf.map (homOfLE (pair_le_remove U (pairIndex i j h) 0)).op
          (s ((pairIndex i j h).remove 0)) -
        F.presheaf.map (homOfLE (pair_le_remove U (pairIndex i j h) 1)).op
          (s ((pairIndex i j h).remove 1)) := by
  rw [orderedCechDifferential, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul]
  change
    F.presheaf.map _ (s ((pairIndex i j h).remove 0)) +
      -F.presheaf.map _ (s ((pairIndex i j h).remove 1)) = _
  rw [sub_eq_add_neg]

/-- The concrete kernel in degree zero of the ordered Cech complex. -/
abbrev Kernel (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :=
  (((orderedCechComplex U F).sc 0).g).hom.ker

/-- The concrete additive-group kernel fork for the first ordered Cech differential. -/
def kernelFork (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    KernelFork ((orderedCechComplex U F).sc 0).g :=
  KernelFork.ofι
    (AddCommGrpCat.ofHom (AddSubgroup.subtype (((orderedCechComplex U F).sc 0).g).hom.ker))
    (by ext s; exact s.2)

private def kernelForkIsLimit (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    IsLimit (kernelFork U F) :=
  IsLimit.ofIsoLimit (kernelIsKernel ((orderedCechComplex U F).sc 0).g)
    (Fork.ext (AddCommGrpCat.kernelIsoKer ((orderedCechComplex U F).sc 0).g)
      (AddCommGrpCat.kernelIsoKer_hom_comp_subtype _))

private theorem mem_kernel_differential (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) (s : Kernel U F) :
    orderedCechDifferential U F 0 s.1 = 0 := by
  have hs := s.2
  change
    (orderedCechComplex U F).d 0 ((ComplexShape.up ℕ).next 0) s.1 = 0 at hs
  rw [CochainComplex.next] at hs
  exact hs

/-- A morphism of sheaves sends degree-zero cocycles to degree-zero cocycles. -/
def kernelMap (U : ι → Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) : AddCommGrpCat.of (Kernel U F) ⟶ AddCommGrpCat.of (Kernel U G) :=
  AddCommGrpCat.ofHom
    { toFun := fun s =>
        let c : orderedCechCochains U F 0 := s.1
        ⟨orderedCechCochainsMap U f 0 c, by
          change
            (orderedCechComplex U G).d 0 ((ComplexShape.up ℕ).next 0)
              (orderedCechCochainsMap U f 0 c) = 0
          rw [CochainComplex.next]
          dsimp [orderedCechComplex]
          dsimp [CochainComplex.of.d]
          change orderedCechDifferential U G 0
            (orderedCechCochainsMap U f 0 c) = 0
          have h := ConcreteCategory.congr_hom
            (orderedCechDifferential_naturality U f 0) c
          simp only [ConcreteCategory.comp_apply] at h
          have hc : orderedCechDifferential U F 0 c = 0 := by
            dsimp [c]
            exact mem_kernel_differential U F s
          rw [h, hc, map_zero]⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero _
      map_add' := by
        intro s t
        apply Subtype.ext
        exact map_add _ _ _ }

private theorem restrict_congr (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (s : orderedCechCochains U F 0) (V : Opens X)
    {a b : OrderedCechIndex ι 0} (hab : a = b)
    (ha : V ≤ orderedCechIntersection U a)
    (hb : V ≤ orderedCechIntersection U b) :
    F.presheaf.map (homOfLE ha).op (s a) =
      F.presheaf.map (homOfLE hb).op (s b) := by
  subst b
  congr

private theorem transport_restrict (F : X.Sheaf AddCommGrpCat.{u})
    {V W T : Opens X} (hWT : W = T) (hWV : W ≤ V) (hTV : T ≤ V)
    (x : F.presheaf.obj (op V)) :
    F.presheaf.map (eqToHom hWT.symm).op
        (F.presheaf.map (homOfLE hWV).op x) =
      F.presheaf.map (homOfLE hTV).op x := by
  subst T
  simp

private theorem kernel_compatible_of_lt (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) (s : Kernel U F)
    (i j : ι) (h : i < j) :
    F.presheaf.map
        (infLELeft (opens U (singletonIndex i)) (opens U (singletonIndex j))).op
        (s.1 (singletonIndex i)) =
      F.presheaf.map
        (infLERight (opens U (singletonIndex i)) (opens U (singletonIndex j))).op
        (s.1 (singletonIndex j)) := by
  let c : orderedCechCochains U F 0 := s.1
  change
    F.presheaf.map
        (infLELeft (opens U (singletonIndex i)) (opens U (singletonIndex j))).op
        (c (singletonIndex i)) =
      F.presheaf.map
        (infLERight (opens U (singletonIndex i)) (opens U (singletonIndex j))).op
        (c (singletonIndex j))
  let a := pairIndex i j h
  let W := orderedCechIntersection U a
  let T := opens U (singletonIndex i) ⊓ opens U (singletonIndex j)
  have hWT : W = T := by
    dsimp [W, T, a, opens]
    simp
  have hWi : W ≤ opens U (singletonIndex i) := by
    dsimp [W, a, opens]
    rw [intersection_pairIndex, intersection_singletonIndex]
    exact inf_le_left
  have hWj : W ≤ opens U (singletonIndex j) := by
    dsimp [W, a, opens]
    rw [intersection_pairIndex, intersection_singletonIndex]
    exact inf_le_right
  have hremoveZero : a.remove 0 = singletonIndex j := by
    simp [a]
  have hremoveOne : a.remove 1 = singletonIndex i := by
    simp [a]
  have hc : orderedCechDifferential U F 0 c = 0 := by
    dsimp [c]
    exact mem_kernel_differential U F s
  have hd0 := congrFun hc a
  have hd :
      F.presheaf.map (homOfLE (pair_le_remove U a 0)).op (c (a.remove 0)) =
        F.presheaf.map (homOfLE (pair_le_remove U a 1)).op (c (a.remove 1)) := by
    simp only at hd0
    dsimp [a] at hd0
    rw [differential_zero_apply_pair] at hd0
    exact sub_eq_zero.mp hd0
  have hjW :
      F.presheaf.map (homOfLE (pair_le_remove U a 0)).op (c (a.remove 0)) =
        F.presheaf.map (homOfLE hWj).op (c (singletonIndex j)) :=
    restrict_congr U F c W hremoveZero _ _
  have hiW :
      F.presheaf.map (homOfLE (pair_le_remove U a 1)).op (c (a.remove 1)) =
        F.presheaf.map (homOfLE hWi).op (c (singletonIndex i)) :=
    restrict_congr U F c W hremoveOne _ _
  let tr := F.presheaf.map (eqToHom hWT.symm).op
  have hdT := congrArg (fun z => tr z) hd
  have hjT := congrArg (fun z => tr z) hjW
  have hiT := congrArg (fun z => tr z) hiW
  have hjTarget :
      tr (F.presheaf.map (homOfLE (pair_le_remove U a 0)).op (c (a.remove 0))) =
        F.presheaf.map
          (infLERight (opens U (singletonIndex i)) (opens U (singletonIndex j))).op
          (c (singletonIndex j)) := by
    rw [hjT]
    exact transport_restrict F hWT hWj inf_le_right _
  have hiTarget :
      tr (F.presheaf.map (homOfLE (pair_le_remove U a 1)).op (c (a.remove 1))) =
        F.presheaf.map
          (infLELeft (opens U (singletonIndex i)) (opens U (singletonIndex j))).op
          (c (singletonIndex i)) := by
    rw [hiT]
    exact transport_restrict F hWT hWi inf_le_left _
  exact hiTarget.symm.trans (hdT.symm.trans hjTarget)

private theorem compatible_congr (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) (c : orderedCechCochains U F 0)
    {a a' b b' : OrderedCechIndex ι 0} (ha : a' = a) (hb : b' = b)
    (h :
      F.presheaf.map (infLELeft (opens U a') (opens U b')).op (c a') =
        F.presheaf.map (infLERight (opens U a') (opens U b')).op (c b')) :
    F.presheaf.map (infLELeft (opens U a) (opens U b)).op (c a) =
      F.presheaf.map (infLERight (opens U a) (opens U b)).op (c b) := by
  subst a
  subst b
  exact h

private theorem compatible_symm (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) (c : orderedCechCochains U F 0)
    {a b : OrderedCechIndex ι 0}
    (h :
      F.presheaf.map (infLELeft (opens U b) (opens U a)).op (c b) =
        F.presheaf.map (infLERight (opens U b) (opens U a)).op (c a)) :
    F.presheaf.map (infLELeft (opens U a) (opens U b)).op (c a) =
      F.presheaf.map (infLERight (opens U a) (opens U b)).op (c b) := by
  let W := opens U b ⊓ opens U a
  let T := opens U a ⊓ opens U b
  have hWT : W = T := by
    dsimp [W, T]
    exact inf_comm _ _
  let tr := F.presheaf.map (eqToHom hWT.symm).op
  have hT := congrArg (fun z => tr z) h.symm
  have haT :
      tr (F.presheaf.map (infLERight (opens U b) (opens U a)).op (c a)) =
        F.presheaf.map (infLELeft (opens U a) (opens U b)).op (c a) :=
    transport_restrict F hWT inf_le_right inf_le_left _
  have hbT :
      tr (F.presheaf.map (infLELeft (opens U b) (opens U a)).op (c b)) =
        F.presheaf.map (infLERight (opens U a) (opens U b)).op (c b) :=
    transport_restrict F hWT inf_le_left inf_le_right _
  exact haT.symm.trans (hT.trans hbT)

private theorem kernel_compatible (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) (s : Kernel U F) :
    TopCat.Presheaf.IsCompatible F.presheaf (opens U) s.1 := by
  intro a b
  have ha : singletonIndex (a.1 0) = a := singletonIndex_value a
  have hb : singletonIndex (b.1 0) = b := singletonIndex_value b
  rcases lt_trichotomy (a.1 0) (b.1 0) with hij | hij | hij
  · exact compatible_congr U F s.1 ha hb (kernel_compatible_of_lt U F s _ _ hij)
  · have hab : a = b := by
      calc
        a = singletonIndex (a.1 0) := ha.symm
        _ = singletonIndex (b.1 0) := congrArg singletonIndex hij
        _ = b := hb
    subst b
    congr
  · exact compatible_congr U F s.1 ha hb
      (compatible_symm U F s.1 (kernel_compatible_of_lt U F s _ _ hij))

/-- Restrict a section over the union of the cover to every degree-zero intersection. -/
def restrictCochain (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (x : F.presheaf.obj (op (iSup (opens U)))) : orderedCechCochains U F 0 :=
  fun a => F.presheaf.map (leSupr (opens U) a).op x

private theorem restrictCochain_differential (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u})
    (x : F.presheaf.obj (op (iSup (opens U)))) :
    orderedCechDifferential U F 0 (restrictCochain U F x) = 0 := by
  funext a
  rw [orderedCechDifferential, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul]
  change
    F.presheaf.map _
          (F.presheaf.map (leSupr (opens U) (a.remove 0)).op x) +
      -F.presheaf.map _
          (F.presheaf.map (leSupr (opens U) (a.remove 1)).op x) = 0
  have h0 :
      F.presheaf.map (homOfLE (pair_le_remove U a 0)).op
          (F.presheaf.map (leSupr (opens U) (a.remove 0)).op x) =
        F.presheaf.map
          (homOfLE ((pair_le_remove U a 0).trans
            (le_iSup (opens U) (a.remove 0)))).op x := by
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
    rw [show
      (leSupr (opens U) (a.remove 0)).op ≫
          (homOfLE (pair_le_remove U a 0)).op =
        (homOfLE ((pair_le_remove U a 0).trans
          (le_iSup (opens U) (a.remove 0)))).op from Subsingleton.elim _ _]
  have h1 :
      F.presheaf.map (homOfLE (pair_le_remove U a 1)).op
          (F.presheaf.map (leSupr (opens U) (a.remove 1)).op x) =
        F.presheaf.map
          (homOfLE ((pair_le_remove U a 1).trans
            (le_iSup (opens U) (a.remove 1)))).op x := by
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
    rw [show
      (leSupr (opens U) (a.remove 1)).op ≫
          (homOfLE (pair_le_remove U a 1)).op =
        (homOfLE ((pair_le_remove U a 1).trans
          (le_iSup (opens U) (a.remove 1)))).op from Subsingleton.elim _ _]
  rw [h0, h1]
  have hmap :
      F.presheaf.map
          (homOfLE ((pair_le_remove U a 1).trans
            (le_iSup (opens U) (a.remove 1)))).op =
        F.presheaf.map
          (homOfLE ((pair_le_remove U a 0).trans
            (le_iSup (opens U) (a.remove 0)))).op := by
    congr
  rw [hmap, add_neg_cancel]

/-- The degree-zero cocycle obtained by restricting a section over the union. -/
def restrictToKernel (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (x : F.presheaf.obj (op (iSup (opens U)))) : Kernel U F :=
  ⟨restrictCochain U F x, by
    change
      (orderedCechComplex U F).d 0 ((ComplexShape.up ℕ).next 0)
        (restrictCochain U F x) = 0
    rw [CochainComplex.next]
    exact restrictCochain_differential U F x⟩

/-- Glue a degree-zero cocycle to a section over the union of the cover. -/
def glue (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (s : Kernel U F) :
    F.presheaf.obj (op (iSup (opens U))) :=
  (F.existsUnique_gluing (opens U) s.1 (kernel_compatible U F s)).choose

@[simp]
theorem glue_restrict (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (s : Kernel U F) (a : OrderedCechIndex ι 0) :
    F.presheaf.map (leSupr (opens U) a).op (glue U F s) = s.1 a :=
  (F.existsUnique_gluing (opens U) s.1 (kernel_compatible U F s)).choose_spec.1 a

theorem glue_naturality (U : ι → Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) (s : Kernel U F) :
    f.hom.app (op (iSup (opens U))) (glue U F s) =
      glue U G (kernelMap U f s) := by
  apply G.eq_of_locally_eq (opens U)
  intro a
  rw [glue_restrict]
  change
    G.presheaf.map (leSupr (opens U) a).op
        (f.hom.app (op (iSup (opens U))) (glue U F s)) =
      f.hom.app (op (opens U a)) (s.1 a)
  calc
    _ = f.hom.app (op (opens U a))
        (F.presheaf.map (leSupr (opens U) a).op (glue U F s)) :=
      (ConcreteCategory.congr_hom
        (f.hom.naturality (leSupr (opens U) a).op) (glue U F s)).symm
    _ = _ := by rw [glue_restrict]

private theorem glue_add (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (s t : Kernel U F) :
    glue U F (s + t) = glue U F s + glue U F t := by
  apply F.eq_of_locally_eq (opens U)
  intro a
  rw [map_add, glue_restrict, glue_restrict, glue_restrict]
  rfl

/-- Degree-zero cocycles are additively equivalent to sections over the union of the cover. -/
def kernelEquivSections (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    Kernel U F ≃+ F.presheaf.obj (op (iSup (opens U))) where
  toFun := glue U F
  invFun := restrictToKernel U F
  left_inv s := by
    apply Subtype.ext
    funext a
    exact glue_restrict U F s a
  right_inv x := by
    apply F.eq_of_locally_eq (opens U)
    intro a
    rw [glue_restrict]
    rfl
  map_add' := glue_add U F

theorem kernelEquivSections_naturality (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    kernelMap U f ≫ (kernelEquivSections U G).toAddCommGrpIso.hom =
      (kernelEquivSections U F).toAddCommGrpIso.hom ≫
        f.hom.app (op (iSup (opens U))) := by
  ext s
  exact (glue_naturality U f s).symm

private theorem incoming_zero (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((orderedCechComplex U F).sc 0).f = 0 := by
  change (orderedCechComplex U F).d ((ComplexShape.up ℕ).prev 0) 0 = 0
  rw [CochainComplex.prev_nat_zero]
  apply (orderedCechComplex U F).shape
  simp

/-- Homology data in degree zero using the concrete kernel of the first differential. -/
def homologyData (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((orderedCechComplex U F).sc 0).HomologyData :=
  .ofIsLimitKernelFork ((orderedCechComplex U F).sc 0) (incoming_zero U F)
    (kernelFork U F) (kernelForkIsLimit U F)

/-- The action on the concrete degree-zero homology data induced by a sheaf morphism. -/
def homologyMapData (U : ι → Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) :
    ShortComplex.HomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) 0).map
        (orderedCechComplexMap U f))
      (homologyData U F) (homologyData U G) :=
  .ofIsLimitKernelFork _ (incoming_zero U F) (kernelFork U F) (kernelForkIsLimit U F)
    (incoming_zero U G) (kernelFork U G) (kernelForkIsLimit U G) (kernelMap U f) (by
      ext s
      rfl)

private theorem homologyMapData_φH (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    (homologyMapData U f).left.φH = kernelMap U f :=
  rfl

private theorem homologyMapData_kernelEquiv_naturality (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    (homologyMapData U f).left.φH ≫
        (kernelEquivSections U G).toAddCommGrpIso.hom =
      (kernelEquivSections U F).toAddCommGrpIso.hom ≫
        f.hom.app (op (iSup (opens U))) := by
  rw [homologyMapData_φH]
  exact kernelEquivSections_naturality U f

private def scHomologyIsoSectionsUnion (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    ((orderedCechComplex U F).sc 0).homology ≅
      F.presheaf.obj (op (iSup (opens U))) :=
  (homologyData U F).left.homologyIso ≪≫
    (kernelEquivSections U F).toAddCommGrpIso

private theorem scHomologyIsoSectionsUnion_hom (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    (scHomologyIsoSectionsUnion U F).hom =
      (homologyData U F).left.homologyIso.hom ≫
        (kernelEquivSections U F).toAddCommGrpIso.hom :=
  rfl

/-- Zeroth ordered Cech cohomology is the group of sections over the union of the cover. -/
def homologyIsoSectionsUnion (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    orderedCechCohomology U F 0 ≅ F.presheaf.obj (op (iSup (opens U))) :=
  scHomologyIsoSectionsUnion U F

private theorem scHomologyIsoSectionsUnion_naturality (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) 0).map
            (orderedCechComplexMap U f)) ≫
        (scHomologyIsoSectionsUnion U G).hom =
      (scHomologyIsoSectionsUnion U F).hom ≫
        f.hom.app (op (iSup (opens U))) := by
  rw [scHomologyIsoSectionsUnion_hom, scHomologyIsoSectionsUnion_hom,
    ← Category.assoc,
    (homologyMapData U f).left.homologyMap_comm]
  simp only [Category.assoc]
  rw [homologyMapData_kernelEquiv_naturality]

theorem homologyIsoSectionsUnion_naturality (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    (orderedCechCohomologyFunctor U 0).map f ≫ (homologyIsoSectionsUnion U G).hom =
      (homologyIsoSectionsUnion U F).hom ≫ f.hom.app (op (iSup (opens U))) := by
  exact scHomologyIsoSectionsUnion_naturality U f

/-- The natural isomorphism from zeroth ordered Cech cohomology to sections over the union. -/
def homologyNatIsoSectionsUnion (U : ι → Opens X) :
    orderedCechCohomologyFunctor U 0 ≅ sectionsFunctor (iSup (opens U)) :=
  NatIso.ofComponents (homologyIsoSectionsUnion U)
    (fun f => homologyIsoSectionsUnion_naturality U f)

/-- Evaluation on equal opens gives naturally isomorphic section functors. -/
def sectionsFunctorIsoOfEq {V W : Opens X} (h : V = W) :
    sectionsFunctor V ≅ sectionsFunctor W := by
  subst W
  exact Iso.refl _

end CechZero

/-- For an open cover, zeroth ordered Cech cohomology is naturally isomorphic to global
sections. -/
def orderedCechH0NatIsoGlobalSections (U : ι → Opens X) (hU : IsOpenCover U) :
    orderedCechCohomologyFunctor U 0 ≅ CechZero.sectionsFunctor (⊤ : Opens X) :=
  CechZero.homologyNatIsoSectionsUnion U ≪≫
    CechZero.sectionsFunctorIsoOfEq ((CechZero.iSup_opens U).trans hU.iSup_eq_top)

/-- The component at `F` of the natural isomorphism identifying zeroth ordered Cech cohomology
with global sections. -/
def orderedCechH0IsoGlobalSections (U : ι → Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) (hU : IsOpenCover U) :
    orderedCechCohomology U F 0 ≅ F.presheaf.obj (op ⊤) :=
  (orderedCechH0NatIsoGlobalSections U hU).app F

theorem orderedCechH0IsoGlobalSections_naturality (U : ι → Opens X)
    (hU : IsOpenCover U) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    (orderedCechCohomologyFunctor U 0).map f ≫
        (orderedCechH0IsoGlobalSections U G hU).hom =
      (orderedCechH0IsoGlobalSections U F hU).hom ≫ f.hom.app (op ⊤) :=
  (orderedCechH0NatIsoGlobalSections U hU).hom.naturality f

end Hartshorne
