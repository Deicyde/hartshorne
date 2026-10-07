/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Order.Fin.Tuple
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# The ordered normalized Cech complex

Hartshorne, *Algebraic Geometry*, III.4 (pp. 218--219).

For a linearly ordered open cover, the degree-`p` cochains are products over strictly increasing
`(p+1)`-tuples.  The differential is the alternating sum of restrictions obtained by deleting one
index.  Thus repeated indices are absent by construction rather than retained as in the all-tuples
Cech nerve.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

namespace Hartshorne

universe u

/-- Strictly increasing `(p+1)`-tuples of indices for the ordered Cech complex. -/
def OrderedCechIndex (ι : Type u) [LinearOrder ι] (p : ℕ) :=
  { a : Fin (p + 1) → ι // StrictMono a }

namespace OrderedCechIndex

variable {ι : Type u} [LinearOrder ι]

/-- Delete one entry from a strictly increasing tuple. -/
def remove {p : ℕ} (a : OrderedCechIndex ι (p + 1)) (q : Fin (p + 2)) :
    OrderedCechIndex ι p :=
  ⟨q.removeNth a.1, a.2.removeNth q⟩

@[simp]
theorem remove_apply {p : ℕ} (a : OrderedCechIndex ι (p + 1))
    (q : Fin (p + 2)) (j : Fin (p + 1)) :
    (a.remove q).1 j = a.1 (q.succAbove j) :=
  rfl

end OrderedCechIndex

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]

/-- The intersection indexed by an increasing Cech tuple. -/
def orderedCechIntersection (U : ι → Opens X) {p : ℕ}
    (a : OrderedCechIndex ι p) : Opens X :=
  ⨅ j, U (a.1 j)

private theorem orderedCechIntersection_le_remove
    (U : ι → Opens X) {p : ℕ} (a : OrderedCechIndex ι (p + 1))
    (q : Fin (p + 2)) :
    orderedCechIntersection U a ≤ orderedCechIntersection U (a.remove q) := by
  rw [orderedCechIntersection, orderedCechIntersection]
  refine le_iInf fun j ↦ ?_
  exact iInf_le_of_le (q.succAbove j) le_rfl

/-- Degree-`p` ordered Cech cochains. -/
def orderedCechCochains (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (∀ a : OrderedCechIndex ι p,
    F.presheaf.obj (op (orderedCechIntersection U a)))

/-- A morphism of sheaves acts componentwise on ordered Cech cochains. -/
def orderedCechCochainsMap (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (p : ℕ) :
    orderedCechCochains U F p ⟶ orderedCechCochains U G p :=
  AddCommGrpCat.ofHom
    { toFun := fun s a => f.hom.app _ (s a)
      map_zero' := by
        ext a
        exact map_zero _
      map_add' := by
        intro s t
        ext a
        exact map_add _ _ _ }

/-- Degree-`p` ordered Cech cochains, functorial in the sheaf. -/
def orderedCechCochainsFunctor (U : ι → Opens X) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj F := orderedCechCochains U F p
  map f := orderedCechCochainsMap U f p
  map_id F := by
    ext s
    apply funext
    intro a
    rfl
  map_comp f g := by
    ext s
    apply funext
    intro a
    rfl

/-- The `q`th coface map: restrict from the intersection with the `q`th index deleted to the full
intersection. -/
def orderedCechCoface (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) (q : Fin (p + 2)) :
    orderedCechCochains U F p ⟶ orderedCechCochains U F (p + 1) :=
  AddCommGrpCat.ofHom
    { toFun := fun s a ↦
        F.presheaf.map (homOfLE (orderedCechIntersection_le_remove U a q)).op
          (s (a.remove q))
      map_zero' := by
        ext a
        exact map_zero _
      map_add' := by
        intro s t
        ext a
        exact map_add _ _ _ }

@[reassoc]
theorem orderedCechCoface_naturality (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (p : ℕ) (q : Fin (p + 2)) :
    orderedCechCochainsMap U f p ≫ orderedCechCoface U G p q =
      orderedCechCoface U F p q ≫ orderedCechCochainsMap U f (p + 1) := by
  ext s
  apply funext
  intro a
  change
    G.presheaf.map _ (f.hom.app _ (s (a.remove q))) =
      f.hom.app _ (F.presheaf.map _ (s (a.remove q)))
  exact (ConcreteCategory.congr_hom
    (f.hom.naturality
      (homOfLE (orderedCechIntersection_le_remove U a q)).op)
    (s (a.remove q))).symm

/-- The alternating ordered Cech differential. -/
def orderedCechDifferential (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) : orderedCechCochains U F p ⟶ orderedCechCochains U F (p + 1) :=
  ∑ q : Fin (p + 2), (-1 : ℤ) ^ (q : ℕ) • orderedCechCoface U F p q

@[reassoc]
theorem orderedCechDifferential_naturality (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (p : ℕ) :
    orderedCechCochainsMap U f p ≫ orderedCechDifferential U G p =
      orderedCechDifferential U F p ≫ orderedCechCochainsMap U f (p + 1) := by
  simp only [orderedCechDifferential, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro q _
  rw [orderedCechCoface_naturality]

private theorem orderedCech_restrict_congr
    (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) {p : ℕ}
    (s : ∀ b : OrderedCechIndex ι p,
      F.presheaf.obj (op (orderedCechIntersection U b)))
    (V : Opens X) {b c : OrderedCechIndex ι p} (h : b = c)
    (hb : V ≤ orderedCechIntersection U b)
    (hc : V ≤ orderedCechIntersection U c) :
    F.presheaf.map (homOfLE hb).op (s b) =
      F.presheaf.map (homOfLE hc).op (s c) := by
  subst c
  congr

private theorem orderedCechCoface_comp
    (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    (i : Fin (p + 2)) (j : Fin (p + 3)) :
    orderedCechCoface U F p i ≫ orderedCechCoface U F (p + 1) j =
      orderedCechCoface U F p (i.predAbove j) ≫
        orderedCechCoface U F (p + 1) (j.succAbove i) := by
  ext s
  apply funext
  intro a
  change
    F.presheaf.map _
        (F.presheaf.map _ (s ((a.remove j).remove i))) =
      F.presheaf.map _
        (F.presheaf.map _ (s ((a.remove (j.succAbove i)).remove (i.predAbove j))))
  let b := (a.remove j).remove i
  let c := (a.remove (j.succAbove i)).remove (i.predAbove j)
  have hremove :
      b = c := by
    apply Subtype.ext
    exact Fin.removeNth_removeNth_eq_swap a.1 i j
  have hb : orderedCechIntersection U a ≤ orderedCechIntersection U b :=
    (orderedCechIntersection_le_remove U a j).trans
      (orderedCechIntersection_le_remove U (a.remove j) i)
  have hc : orderedCechIntersection U a ≤ orderedCechIntersection U c :=
    (orderedCechIntersection_le_remove U a (j.succAbove i)).trans
      (orderedCechIntersection_le_remove U (a.remove (j.succAbove i)) (i.predAbove j))
  calc
    _ = F.presheaf.map (homOfLE hb).op (s b) := by
      rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
      rw [show
        (homOfLE (orderedCechIntersection_le_remove U (a.remove j) i)).op ≫
            (homOfLE (orderedCechIntersection_le_remove U a j)).op =
          (homOfLE hb).op from Subsingleton.elim _ _]
    _ = F.presheaf.map (homOfLE hc).op (s c) :=
      orderedCech_restrict_congr U F s _ hremove hb hc
    _ = _ := by
      rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
      rw [show
        (homOfLE (orderedCechIntersection_le_remove U
            (a.remove (j.succAbove i)) (i.predAbove j))).op ≫
            (homOfLE (orderedCechIntersection_le_remove U a (j.succAbove i))).op =
          (homOfLE hc).op from Subsingleton.elim _ _]

private theorem orderedCechDifferential_squared
    (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    orderedCechDifferential U F p ≫ orderedCechDifferential U F (p + 1) = 0 := by
  dsimp [orderedCechDifferential]
  simp only [Preadditive.sum_comp]
  simp only [Preadditive.comp_sum, ← Finset.sum_product']
  let P := Fin (p + 2) × Fin (p + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij ↦
    (Fin.castLT ij.2
      (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    have hji : (j : ℕ) ≤ (i : ℕ) := (Finset.mem_filter.mp hij).2
    have hj : j < i.succ := by
      exact Fin.mk_lt_mk.mpr (Nat.lt_succ_of_le hji)
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      smul_smul, ← neg_smul]
    congr 1
    · dsimp [φ]
      simp only [pow_add, pow_one]
      ring
    · rw [orderedCechCoface_comp]
      congr 2
      · rw [Fin.predAbove_of_lt_succ _ _ hj]
        apply Fin.ext
        rfl
      · exact Fin.succAbove_of_lt_succ _ _ hj

/-- The ordered normalized Cech cochain complex. -/
noncomputable def orderedCechComplex
    (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (orderedCechCochains U F)
    (orderedCechDifferential U F) (orderedCechDifferential_squared U F)

/-- A morphism of sheaves induces a morphism of ordered Cech complexes. -/
def orderedCechComplexMap (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    orderedCechComplex U F ⟶ orderedCechComplex U G where
  f p := orderedCechCochainsMap U f p
  comm' p q hpq := by
    have hpq' : p + 1 = q := by
      simpa only [ComplexShape.up_Rel] using hpq
    subst q
    dsimp [orderedCechComplex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact orderedCechDifferential_naturality U f p

/-- The ordered Cech complex, functorial in the sheaf. -/
def orderedCechComplexFunctor (U : ι → Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ CochainComplex AddCommGrpCat.{u} ℕ where
  obj F := orderedCechComplex U F
  map f := orderedCechComplexMap U f
  map_id F := by
    apply HomologicalComplex.hom_ext
    intro p
    exact (orderedCechCochainsFunctor U p).map_id F
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro p
    exact (orderedCechCochainsFunctor U p).map_comp f g

/-- Degree-`p` ordered Cech cohomology. -/
noncomputable def orderedCechCohomology
    (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    AddCommGrpCat.{u} :=
  (orderedCechComplex U F).homology p

/-- Ordered Cech cohomology in degree `p`, functorial in the sheaf. -/
def orderedCechCohomologyFunctor (U : ι → Opens X) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  orderedCechComplexFunctor U ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p

end Hartshorne
