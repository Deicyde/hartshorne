/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.OrderedCechComplex
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The sheafified Cech resolution

Hartshorne, *Algebraic Geometry*, III, Lemma 4.2 (pp. 220--221).

Let `U = (U_i)` be a family of open sets of `X` indexed by a linearly ordered type and `F` an
abelian sheaf.  For an increasing tuple `a = (i_0 < ⋯ < i_p)` write `U_a` for the intersection
and `f_a : U_a → X` for the inclusion.  The sheaf `𝒞^p(U, F)` has sections over `V` the ordered
Cech cochains of the cover `(V ∩ U_i)` of `V`, that is `∏_a F(V ∩ U_a)`, with the ordered Cech
differential; it is the product of the direct images `(f_a)_* (F|U_a)`.

## Main definitions and results

* `Hartshorne.SheafifiedCech.cochainSheaf`: the sheaf `𝒞^p(U, F)`, and
  `Hartshorne.SheafifiedCech.cochainSheafIsProduct`, which exhibits it, with its projections, as
  the product over increasing tuples `a` of the direct images `(f_a)_* (F|U_a)` (Mathlib's
  `TopCat.Sheaf.pushforward` of `Opens.sheafRestrict`).
* `Hartshorne.SheafifiedCech.sheafifiedCechComplex`: the complex `𝒞^•(U, F)` of sheaves, and
  `Hartshorne.SheafifiedCech.augmentedSheafifiedCechComplex`, the complex
  `0 → F → 𝒞^0(U, F) → 𝒞^1(U, F) → ⋯` obtained from the augmentation
  `Hartshorne.SheafifiedCech.augmentation`.
* `Hartshorne.SheafifiedCech.augmentedSheafifiedCechComplex_exactAt`: when `U` covers `X`, the
  augmented complex is exact in every degree.
* `Hartshorne.SheafifiedCech.globalSectionsIso`: applying the global sections functor to
  `𝒞^•(U, F)` gives the ordered Cech complex `Hartshorne.orderedCechComplex U F`.

## Naturality in the sheaf

* `Hartshorne.SheafifiedCech.sheafifiedCechComplexFunctor` and
  `Hartshorne.SheafifiedCech.augmentedSheafifiedCechComplexFunctor`: `𝒞^•(U, -)` and the
  augmented complex as functors from abelian sheaves to complexes of sheaves, built from the
  squares `Hartshorne.SheafifiedCech.augmentation_naturality` and
  `Hartshorne.SheafifiedCech.cochainSheafMap_comp_cochainDifferential`.
* `Hartshorne.SheafifiedCech.augmentationNatTrans`: the augmentations, as morphisms of complexes
  `Hartshorne.SheafifiedCech.augmentationHom` from `F` placed in degree zero, form a natural
  transformation; `Hartshorne.SheafifiedCech.quasiIso_augmentationHom` says each is a
  quasi-isomorphism when `U` covers `X`.
* `Hartshorne.SheafifiedCech.globalSectionsNatIso`: the global-sections isomorphisms with the
  ordered Cech complex are natural in the sheaf.

## Proof

Exactness is checked on stalks (`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`).  Near a point
`x ∈ U_j`, on sections over an open `V ⊆ U_j`, inserting the index `j` into increasing tuples
(with the sign of the insertion position, and zero when `j` already occurs) defines a contracting
homotopy of the augmented complex; this is Hartshorne's homotopy written for strictly increasing
tuples.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hartshorne

universe u

namespace OrderedCechIndex

variable {ι : Type u} [LinearOrder ι]

theorem ext_of_range {p : ℕ} {a b : OrderedCechIndex ι p}
    (h : Set.range a.1 = Set.range b.1) : a = b :=
  Subtype.ext ((a.2.range_inj b.2).1 h)

theorem range_remove {p : ℕ} (a : OrderedCechIndex ι (p + 1)) (r : Fin (p + 2)) :
    Set.range (a.remove r).1 = Set.range a.1 \ {a.1 r} := by
  have : (a.remove r).1 = a.1 ∘ r.succAbove := rfl
  rw [this, Set.range_comp, Fin.range_succAbove,
    Set.image_compl_eq_range_sdiff_image a.2.injective, Set.image_singleton]

/-- The position at which `j` is inserted into an increasing tuple: the number of entries less
than `j`. -/
def insertPos {p : ℕ} (j : ι) (a : OrderedCechIndex ι p) : Fin (p + 2) :=
  ⟨(Finset.univ.filter fun k => a.1 k < j).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

theorem lt_iff_lt_insertPos {p : ℕ} {j : ι} {a : OrderedCechIndex ι p}
    (hj : j ∉ Set.range a.1) (k : Fin (p + 1)) :
    a.1 k < j ↔ (k : ℕ) < insertPos j a := by
  constructor
  · intro hk
    have hsub : Finset.Iic k ⊆ Finset.univ.filter fun k => a.1 k < j := by
      intro k' hk'
      simp only [Finset.mem_Iic] at hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (a.2.monotone hk') hk
    have := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at this
    exact this
  · intro hk
    by_contra hk'
    have hne : a.1 k ≠ j := fun h => hj ⟨k, h⟩
    have hgt : j < a.1 k := lt_of_le_of_ne (not_lt.mp hk') hne.symm
    have hsub : (Finset.univ.filter fun k => a.1 k < j) ⊆ Finset.Iio k := by
      intro k' hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk'
      simp only [Finset.mem_Iio]
      exact a.2.lt_iff_lt.mp (hk'.trans hgt)
    have := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at this
    exact absurd hk (not_lt.mpr this)

/-- Insert an index not already present into an increasing tuple. -/
def insertIdx {p : ℕ} (j : ι) (a : OrderedCechIndex ι p) (hj : j ∉ Set.range a.1) :
    OrderedCechIndex ι (p + 1) :=
  ⟨(insertPos j a).insertNth j a.1, by
    rw [Fin.strictMono_insertNth_iff]
    refine ⟨a.2, fun i hi => (lt_iff_lt_insertPos hj i).2 ?_, fun i hi => ?_⟩
    · simpa [Fin.lt_def] using hi
    · have hnot : ¬ a.1 i < j := by
        rw [lt_iff_lt_insertPos hj i]
        simpa [Fin.le_def] using hi
      exact lt_of_le_of_ne (not_lt.mp hnot) (fun h => hj ⟨i, h.symm⟩)⟩

theorem insert_apply_insertPos {p : ℕ} (j : ι) (a : OrderedCechIndex ι p)
    (hj : j ∉ Set.range a.1) : (insertIdx j a hj).1 (insertPos j a) = j := by
  unfold insertIdx
  exact Fin.insertNth_apply_same (α := fun _ => ι) _ _ _

theorem insert_apply_succAbove {p : ℕ} (j : ι) (a : OrderedCechIndex ι p)
    (hj : j ∉ Set.range a.1) (i : Fin (p + 1)) :
    (insertIdx j a hj).1 ((insertPos j a).succAbove i) = a.1 i := by
  unfold insertIdx
  exact Fin.insertNth_apply_succAbove (α := fun _ => ι) _ _ _ _

theorem range_insert {p : ℕ} (j : ι) (a : OrderedCechIndex ι p) (hj : j ∉ Set.range a.1) :
    Set.range (insertIdx j a hj).1 = Set.insert j (Set.range a.1) := by
  unfold insertIdx
  exact Fin.range_insertNth _ _ _

theorem insert_remove_insertPos {p : ℕ} (j : ι) (a : OrderedCechIndex ι p)
    (hj : j ∉ Set.range a.1) : (insertIdx j a hj).remove (insertPos j a) = a := by
  unfold insertIdx
  exact Subtype.ext (Fin.removeNth_insertNth (α := fun _ => ι) _ _ _)

theorem not_mem_range_remove {p : ℕ} {j : ι} {a : OrderedCechIndex ι (p + 1)}
    (hj : j ∉ Set.range a.1) (r : Fin (p + 2)) : j ∉ Set.range (a.remove r).1 := by
  rw [range_remove]
  exact fun h => hj h.1

theorem insert_remove_succAbove {p : ℕ} (j : ι) (a : OrderedCechIndex ι (p + 1))
    (hj : j ∉ Set.range a.1) (r : Fin (p + 2)) :
    (insertIdx j a hj).remove ((insertPos j a).succAbove r) =
      insertIdx j (a.remove r) (not_mem_range_remove hj r) := by
  apply ext_of_range
  rw [range_remove, range_insert, range_insert, range_remove, insert_apply_succAbove]
  ext y
  simp only [Set.insert, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h | h, hne⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, hne⟩
  · rintro (h | ⟨h, hne⟩)
    · subst h
      exact ⟨Or.inl rfl, fun h' => hj ⟨r, h'.symm⟩⟩
    · exact ⟨Or.inr h, hne⟩

private theorem eq_of_lt_iff {N c c' : ℕ} (hc : c ≤ N) (hc' : c' ≤ N)
    (h : ∀ k < N, k < c ↔ k < c') : c = c' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd ((h c (by omega)).2 hlt) (lt_irrefl c)
  · exact absurd ((h c' (by omega)).1 hlt) (lt_irrefl c')

theorem insertPos_remove {p : ℕ} (j : ι) (a : OrderedCechIndex ι (p + 1))
    (hj : j ∉ Set.range a.1) (r : Fin (p + 2)) :
    (insertPos j (a.remove r) : ℕ) =
      if (r : ℕ) < insertPos j a then (insertPos j a : ℕ) - 1 else insertPos j a := by
  have hq := (insertPos j a).2
  have hq' := (insertPos j (a.remove r)).2
  have hpos : ∀ k : Fin (p + 1),
      (k : ℕ) < insertPos j (a.remove r) ↔ (r.succAbove k : ℕ) < insertPos j a := by
    intro k
    rw [← lt_iff_lt_insertPos (not_mem_range_remove hj r), ← lt_iff_lt_insertPos hj]
    rfl
  have hr0 : (r : ℕ) < insertPos j a → 0 < (insertPos j a : ℕ) := fun h => by omega
  apply eq_of_lt_iff (N := p + 1) (by omega) (by split_ifs <;> omega)
  intro k hk
  have := hpos ⟨k, hk⟩
  rw [this]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all <;> omega

theorem insertPos_add_succAbove {p : ℕ} (j : ι) (a : OrderedCechIndex ι (p + 1))
    (hj : j ∉ Set.range a.1) (r : Fin (p + 2)) :
    (insertPos j a : ℕ) + ((insertPos j a).succAbove r : ℕ) =
      (r : ℕ) + insertPos j (a.remove r) + 1 := by
  rw [insertPos_remove j a hj r]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all <;> omega

theorem not_mem_range_remove_of_eq {p : ℕ} {j : ι} {a : OrderedCechIndex ι (p + 1)}
    {m : Fin (p + 2)} (hm : a.1 m = j) : j ∉ Set.range (a.remove m).1 := by
  rw [range_remove, hm]
  exact fun h => h.2 rfl

theorem insert_remove_of_eq {p : ℕ} {j : ι} {a : OrderedCechIndex ι (p + 1)}
    {m : Fin (p + 2)} (hm : a.1 m = j) :
    insertIdx j (a.remove m) (not_mem_range_remove_of_eq hm) = a := by
  apply ext_of_range
  rw [range_insert, range_remove, hm]
  have hj : j ∈ Set.range a.1 := ⟨m, hm⟩
  ext y
  simp only [Set.insert, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | ⟨h, _⟩)
    · exact hj
    · exact h
  · intro h
    by_cases hy : y = j
    · exact Or.inl hy
    · exact Or.inr ⟨h, hy⟩

theorem insertPos_remove_of_eq {p : ℕ} {j : ι} {a : OrderedCechIndex ι (p + 1)}
    {m : Fin (p + 2)} (hm : a.1 m = j) : insertPos j (a.remove m) = m := by
  have h := insert_apply_insertPos j (a.remove m) (not_mem_range_remove_of_eq hm)
  rw [insert_remove_of_eq hm] at h
  exact a.2.injective (h.trans hm.symm)

theorem mem_range_remove_of_ne {p : ℕ} {j : ι} {a : OrderedCechIndex ι (p + 1)}
    {m r : Fin (p + 2)} (hm : a.1 m = j) (hr : r ≠ m) : j ∈ Set.range (a.remove r).1 := by
  rw [range_remove]
  refine ⟨⟨m, hm⟩, ?_⟩
  rw [Set.mem_singleton_iff, ← hm]
  exact fun h => hr (a.2.injective h).symm

theorem insert_remove_succAbove_zero (j : ι) (a : OrderedCechIndex ι 0)
    (hj : j ∉ Set.range a.1) :
    (insertIdx j a hj).remove ((insertPos j a).succAbove 0) = ⟨fun _ ↦ j, fun x y hxy ↦
      absurd hxy (by rw [Fin.fin_one_eq_zero x, Fin.fin_one_eq_zero y]; exact lt_irrefl 0)⟩ := by
  apply ext_of_range
  rw [range_remove, range_insert, insert_apply_succAbove]
  have ha : Set.range a.1 = {a.1 0} := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      rw [Fin.fin_one_eq_zero k]
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  have hne : j ≠ a.1 0 := fun h ↦ hj ⟨0, h.symm⟩
  rw [ha]
  ext y
  simp only [Set.insert, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_range,
    exists_const]
  constructor
  · rintro ⟨h | h, h'⟩
    · exact h.symm
    · exact absurd h h'
  · rintro rfl
    exact ⟨Or.inl rfl, fun h ↦ hne h⟩

theorem insertPos_add_succAbove_zero (q : Fin 2) : (q : ℕ) + (q.succAbove 0 : ℕ) = 1 := by
  fin_cases q <;> rfl

end OrderedCechIndex

namespace SheafifiedCech

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]

theorem intersection_le_remove (U : ι → Opens X) {p : ℕ} (a : OrderedCechIndex ι (p + 1))
    (q : Fin (p + 2)) :
    orderedCechIntersection U a ≤ orderedCechIntersection U (a.remove q) :=
  le_iInf fun j ↦ iInf_le_of_le (q.succAbove j) le_rfl

theorem hom_finsetSum {M N : AddCommGrpCat.{u}} {κ : Type*} (t : Finset κ) (f : κ → (M ⟶ N)) :
    (∑ i ∈ t, f i).hom = ∑ i ∈ t, (f i).hom := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, AddCommGrpCat.hom_add, ih]

theorem differential_apply (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    (s : orderedCechCochains U F p) (a : OrderedCechIndex ι (p + 1)) :
    (orderedCechDifferential U F p).hom s a =
      ∑ q : Fin (p + 2), ((-1 : ℤ) ^ (q : ℕ)) •
        F.presheaf.map (homOfLE (intersection_le_remove U a q)).op (s (a.remove q)) := by
  simp only [orderedCechDifferential, hom_finsetSum, AddCommGrpCat.hom_zsmul,
    AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply]
  exact (map_sum (Pi.evalAddMonoidHom
    (fun b : OrderedCechIndex ι (p + 1) => F.presheaf.obj (op (orderedCechIntersection U b))) a)
    (fun q : Fin (p + 2) => ((-1 : ℤ) ^ (q : ℕ)) • (orderedCechCoface U F p q).hom s)
    Finset.univ).trans (Finset.sum_congr rfl fun q _ => rfl)

theorem intersection_mono {U U' : ι → Opens X} (h : ∀ i, U' i ≤ U i) {p : ℕ}
    (a : OrderedCechIndex ι p) :
    orderedCechIntersection U' a ≤ orderedCechIntersection U a :=
  iInf_mono fun _ ↦ h _

/-- Componentwise restriction of ordered Cech cochains along a refinement `U' ≤ U` with the same
index set. -/
def refineCochains {U U' : ι → Opens X} (h : ∀ i, U' i ≤ U i) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) : orderedCechCochains U F p ⟶ orderedCechCochains U' F p :=
  AddCommGrpCat.ofHom
    { toFun := fun s a ↦ F.presheaf.map (homOfLE (intersection_mono h a)).op (s a)
      map_zero' := by
        ext a
        exact map_zero _
      map_add' := by
        intro s t
        ext a
        exact map_add _ _ _ }

theorem refineCochains_apply {U U' : ι → Opens X} (h : ∀ i, U' i ≤ U i)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (s : orderedCechCochains U F p)
    (a : OrderedCechIndex ι p) :
    (refineCochains h F p).hom s a =
      F.presheaf.map (homOfLE (intersection_mono h a)).op (s a) :=
  rfl

theorem refineCochains_coface {U U' : ι → Opens X} (h : ∀ i, U' i ≤ U i)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (q : Fin (p + 2)) :
    refineCochains h F p ≫ orderedCechCoface U' F p q =
      orderedCechCoface U F p q ≫ refineCochains h F (p + 1) := by
  ext s
  apply funext
  intro a
  change F.presheaf.map _ (F.presheaf.map _ (s (a.remove q))) =
    F.presheaf.map _ (F.presheaf.map _ (s (a.remove q)))
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp,
    ← F.presheaf.map_comp]
  rfl

theorem refineCochains_differential {U U' : ι → Opens X} (h : ∀ i, U' i ≤ U i)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    refineCochains h F p ≫ orderedCechDifferential U' F p =
      orderedCechDifferential U F p ≫ refineCochains h F (p + 1) := by
  simp only [orderedCechDifferential, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, refineCochains_coface]

/-- The degree-`p` term of the sheafified Cech complex, as a presheaf: its sections over `V` are
the ordered Cech cochains of the cover `(V ∩ U_i)` of `V`. -/
def cochainPresheaf (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    X.Presheaf AddCommGrpCat.{u} where
  obj V := orderedCechCochains (fun i ↦ V.unop ⊓ U i) F p
  map f := refineCochains (fun i ↦ inf_le_inf_right (U i) f.unop.le) F p
  map_id V := by
    ext s
    apply funext
    intro a
    change F.presheaf.map (𝟙 _) (s a) = s a
    rw [F.presheaf.map_id]
    rfl
  map_comp f g := by
    ext s
    apply funext
    intro a
    change F.presheaf.map _ (s a) = F.presheaf.map _ (F.presheaf.map _ (s a))
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
    rfl

/-- The direct image, along the inclusion of the intersection `U_a`, of the restriction of `F`
to `U_a`. -/
abbrev directImageRestrict (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) {p : ℕ}
    (a : OrderedCechIndex ι p) : X.Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (orderedCechIntersection U a).inclusion').obj
    ((Opens.sheafRestrict (orderedCechIntersection U a)).obj F)

theorem directImageRestrict_open_eq (U : ι → Opens X) {p : ℕ} (a : OrderedCechIndex ι p)
    (V : Opens X) :
    (orderedCechIntersection U a).isOpenEmbedding.isOpenMap.functor.obj
        ((Opens.map (orderedCechIntersection U a).inclusion').obj V) =
      orderedCechIntersection (fun i ↦ V ⊓ U i) a := by
  rw [Opens.functor_obj_map_obj, inf_comm, orderedCechIntersection, orderedCechIntersection,
    ← inf_iInf]
  congr 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

/-- Sections of the direct image of the restriction of `F` to `U_a` over `V` are sections of `F`
over `V ∩ U_a`. -/
def directImageSectionsIso (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) {p : ℕ}
    (a : OrderedCechIndex ι p) (V : Opens X) :
    (directImageRestrict U F a).presheaf.obj (op V) ≅
      F.presheaf.obj (op (orderedCechIntersection (fun i ↦ V ⊓ U i) a)) :=
  F.presheaf.mapIso (eqToIso (directImageRestrict_open_eq U a V).symm).op

/-- The projection from the degree-`p` term to the factor indexed by `a`. -/
def cochainProj (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) {p : ℕ}
    (a : OrderedCechIndex ι p) :
    cochainPresheaf U F p ⟶ (directImageRestrict U F a).presheaf where
  app V := AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ a) ≫
    (directImageSectionsIso U F a V.unop).inv
  naturality V W f := by
    ext s
    change F.presheaf.map _ (F.presheaf.map _ (s a)) = F.presheaf.map _ (F.presheaf.map _ (s a))
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp,
      ← F.presheaf.map_comp]
    rfl

/-- The degree-`p` term with its projections, as a fan over the direct images. -/
def cochainFan (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    Fan (fun a : OrderedCechIndex ι p ↦ (directImageRestrict U F a).presheaf) :=
  Fan.mk (cochainPresheaf U F p) (fun a ↦ cochainProj U F a)

/-- The degree-`p` term is the product of the direct images. -/
def cochainFanIsLimit (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsLimit (cochainFan U F p) := by
  refine evaluationJointlyReflectsLimits _ fun V ↦ ?_
  exact
    { lift := fun c ↦ AddCommGrpCat.ofHom
        { toFun := fun x a ↦ (directImageSectionsIso U F a V.unop).hom (c.π.app ⟨a⟩ x)
          map_zero' := by
            funext a
            simp
          map_add' := by
            intro x y
            funext a
            simp }
      fac := by
        rintro c ⟨a⟩
        ext x
        change (directImageSectionsIso U F a V.unop).inv
          ((directImageSectionsIso U F a V.unop).hom (c.π.app ⟨a⟩ x)) = c.π.app ⟨a⟩ x
        exact Iso.hom_inv_id_apply _ _
      uniq := by
        intro c m hm
        ext x
        funext a
        have h := ConcreteCategory.congr_hom (hm ⟨a⟩) x
        change (directImageSectionsIso U F a V.unop).inv (m.hom x a) = c.π.app ⟨a⟩ x at h
        change m.hom x a = (directImageSectionsIso U F a V.unop).hom (c.π.app ⟨a⟩ x)
        rw [← h]
        exact (Iso.inv_hom_id_apply _ _).symm }

theorem cochainPresheaf_isSheaf (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (cochainPresheaf U F p).IsSheaf :=
  TopCat.isSheaf_of_isLimit
    (Discrete.functor fun a : OrderedCechIndex ι p ↦ (directImageRestrict U F a).presheaf)
    (fun j ↦ (directImageRestrict U F j.as).property) (cochainFanIsLimit U F p)

/-- The degree-`p` sheaf `𝒞^p(U, F)` of the sheafified Cech complex. -/
def cochainSheaf (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{u} :=
  ⟨cochainPresheaf U F p, cochainPresheaf_isSheaf U F p⟩

/-- `𝒞^p(U, F)` is the product, over increasing tuples `a`, of the direct images of the
restrictions of `F` to the intersections `U_a`. -/
def cochainSheafIsProduct (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsLimit (Fan.mk (cochainSheaf U F p)
      (fun a : OrderedCechIndex ι p ↦ ObjectProperty.homMk (cochainProj U F a))) :=
  Fan.IsLimit.mk _
    (fun c ↦ ObjectProperty.homMk
      ((cochainFanIsLimit U F p).lift (Fan.mk c.pt.obj fun a ↦ (c.proj a).hom)))
    (fun c a ↦ by
      apply Sheaf.hom_ext
      exact (cochainFanIsLimit U F p).fac (Fan.mk c.pt.obj fun a ↦ (c.proj a).hom) ⟨a⟩)
    (fun c m hm ↦ by
      apply Sheaf.hom_ext
      exact (cochainFanIsLimit U F p).uniq (Fan.mk c.pt.obj fun a ↦ (c.proj a).hom) m.hom
        (fun j ↦ congrArg (fun f ↦ f.hom) (hm j.as)))

/-- The differential of the sheafified Cech complex: over `V` it is the ordered Cech differential
of the cover `(V ∩ U_i)`. -/
def cochainDifferential (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    cochainSheaf U F p ⟶ cochainSheaf U F (p + 1) :=
  ObjectProperty.homMk
    { app := fun V ↦ orderedCechDifferential (fun i ↦ V.unop ⊓ U i) F p
      naturality := fun _ _ f ↦
        refineCochains_differential (fun i ↦ inf_le_inf_right (U i) f.unop.le) F p }

theorem orderedCechDifferential_comp (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    orderedCechDifferential U F p ≫ orderedCechDifferential U F (p + 1) = 0 := by
  have h := (orderedCechComplex U F).d_comp_d p (p + 1) (p + 1 + 1)
  simp only [orderedCechComplex, CochainComplex.of_d] at h
  exact h

theorem cochainDifferential_comp (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    cochainDifferential U F p ≫ cochainDifferential U F (p + 1) = 0 := by
  apply Sheaf.hom_ext
  ext V : 2
  exact orderedCechDifferential_comp _ F p

/-- The sheafified Cech complex `𝒞^•(U, F)`. -/
def sheafifiedCechComplex (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (cochainSheaf U F) (cochainDifferential U F) (cochainDifferential_comp U F)

theorem sheafifiedCechComplex_d (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (sheafifiedCechComplex U F).d p (p + 1) = cochainDifferential U F p := by
  simp [sheafifiedCechComplex]

theorem intersection_le_left (U : ι → Opens X) (V : Opens X) {p : ℕ}
    (a : OrderedCechIndex ι p) : orderedCechIntersection (fun i ↦ V ⊓ U i) a ≤ V :=
  iInf_le_of_le 0 inf_le_left

/-- The augmentation `F → 𝒞^0(U, F)`, restricting a section to each member of the cover. -/
def augmentation (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    F ⟶ cochainSheaf U F 0 :=
  ObjectProperty.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun s a ↦ F.presheaf.map (homOfLE (intersection_le_left U V.unop a)).op s
          map_zero' := by
            funext a
            exact map_zero _
          map_add' := by
            intro s t
            funext a
            exact map_add _ _ _ }
      naturality := fun V W f ↦ by
        ext s
        funext a
        change F.presheaf.map _ (F.presheaf.map _ s) = F.presheaf.map _ (F.presheaf.map _ s)
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp,
          ← F.presheaf.map_comp]
        rfl }

theorem augmentation_comp_d (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    augmentation U F ≫ (sheafifiedCechComplex U F).d 0 1 = 0 := by
  rw [sheafifiedCechComplex_d]
  apply Sheaf.hom_ext
  ext V s
  apply funext
  intro a
  change (orderedCechDifferential (fun i ↦ V.unop ⊓ U i) F 0).hom
    ((augmentation U F).hom.app V s) a = 0
  refine (differential_apply (fun i ↦ V.unop ⊓ U i) F 0 _ a).trans ?_
  rw [Fin.sum_univ_two]
  change _ • F.presheaf.map _ (F.presheaf.map _ s) + _ • F.presheaf.map _ (F.presheaf.map _ s) = 0
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_smul,
    add_neg_eq_zero]
  change (F.presheaf.map _ ≫ F.presheaf.map _).hom s = (F.presheaf.map _ ≫ F.presheaf.map _).hom s
  rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
  rfl

/-- The augmented sheafified Cech complex `0 → F → 𝒞^0(U, F) → 𝒞^1(U, F) → ⋯`. -/
def augmentedSheafifiedCechComplex (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ :=
  CochainComplex.augment (sheafifiedCechComplex U F) (augmentation U F) (augmentation_comp_d U F)

theorem refineCochains_comp {U U' U'' : ι → Opens X} (h : ∀ i, U' i ≤ U i)
    (h' : ∀ i, U'' i ≤ U' i) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    refineCochains h F p ≫ refineCochains h' F p =
      refineCochains (fun i ↦ (h' i).trans (h i)) F p := by
  ext s
  apply funext
  intro a
  change F.presheaf.map _ (F.presheaf.map _ (s a)) = F.presheaf.map _ (s a)
  rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  rfl

theorem refineCochains_self {U : ι → Opens X} (h : ∀ i, U i ≤ U i)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) : refineCochains h F p = 𝟙 _ := by
  ext s
  apply funext
  intro a
  change F.presheaf.map (𝟙 _) (s a) = s a
  rw [F.presheaf.map_id]
  rfl

/-- The global sections functor on abelian sheaves. -/
abbrev globalSectionsFunctor (X : TopCat.{u}) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

instance (X : TopCat.{u}) : (globalSectionsFunctor X).PreservesZeroMorphisms :=
  inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).PreservesZeroMorphisms

/-- Global sections of `𝒞^p(U, F)` are the ordered Cech cochains `C^p(U, F)`. -/
def globalSectionsCochainIso (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (globalSectionsFunctor X).obj (cochainSheaf U F p) ≅ orderedCechCochains U F p where
  hom := refineCochains (U := fun i ↦ ⊤ ⊓ U i) (fun _ ↦ le_inf le_top le_rfl) F p
  inv := refineCochains (U' := fun i ↦ ⊤ ⊓ U i) (fun _ ↦ inf_le_right) F p
  hom_inv_id := (refineCochains_comp _ _ F p).trans (refineCochains_self _ F p)
  inv_hom_id := (refineCochains_comp _ _ F p).trans (refineCochains_self _ F p)

/-- **Global sections of the sheafified Cech complex.** Applying the global sections functor to
`𝒞^•(U, F)` gives the ordered Cech complex `C^•(U, F)`. -/
def globalSectionsIso (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((globalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (sheafifiedCechComplex U F) ≅ orderedCechComplex U F :=
  HomologicalComplex.Hom.isoOfComponents (fun p ↦ globalSectionsCochainIso U F p) (by
    rintro p _ rfl
    rw [Functor.mapHomologicalComplex_obj_d, sheafifiedCechComplex_d]
    simp only [orderedCechComplex, CochainComplex.of_d]
    exact (refineCochains_differential (U := fun i ↦ ⊤ ⊓ U i)
      (fun i ↦ le_inf le_top le_rfl) F p))

end SheafifiedCech

namespace SheafifiedCech

variable {X : TopCat.{u}}

/-- A short complex of abelian sheaves is exact if, near every point, every section of the middle
term killed by the second map comes from a section of the first term. -/
theorem shortComplex_exact_of_local (S : ShortComplex (X.Sheaf AddCommGrpCat.{u}))
    (h : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ V : Opens X, V ≤ W →
      ∀ b : S.X₂.presheaf.obj (op V), S.g.hom.app (op V) b = 0 →
        ∃ a : S.X₁.presheaf.obj (op V), S.f.hom.app (op V) a = b) :
    S.Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro t ht
  obtain ⟨V, hxV, b, rfl⟩ := S.X₂.presheaf.exists_germ_eq t
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.hom
    (S.X₂.presheaf.germ V x hxV b) = 0 at ht
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ht
  obtain ⟨W', hxW', iU, iV, hW'⟩ := S.X₃.presheaf.germ_eq x hxV hxV _ 0
    (ht.trans (map_zero _).symm)
  rw [map_zero] at hW'
  obtain ⟨W, hxW, hW⟩ := h x
  let i : W' ⊓ W ⟶ V := homOfLE (inf_le_left.trans iU.le)
  obtain ⟨a, ha⟩ := hW (W' ⊓ W) inf_le_right (S.X₂.presheaf.map i.op b) (by
    have hnat := ConcreteCategory.congr_hom (S.g.hom.naturality i.op) b
    change S.g.hom.app (op (W' ⊓ W)) (S.X₂.presheaf.map i.op b) =
      S.X₃.presheaf.map i.op (S.g.hom.app (op V) b) at hnat
    rw [hnat]
    have hi : i = homOfLE inf_le_left ≫ iU := rfl
    rw [hi, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hW', map_zero])
  refine ⟨S.X₁.presheaf.germ (W' ⊓ W) x ⟨hxW', hxW⟩ a, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom
    (S.X₁.presheaf.germ (W' ⊓ W) x ⟨hxW', hxW⟩ a) = _
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (W' ⊓ W) x ⟨hxW', hxW⟩ S.f.hom a).trans ?_
  rw [ha]
  exact TopCat.Presheaf.germ_res_apply S.X₂.presheaf i x ⟨hxW', hxW⟩ b

end SheafifiedCech

namespace SheafifiedCech

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]

theorem map_congr_index (F : X.Sheaf AddCommGrpCat.{u}) {W : ι → Opens X} {p : ℕ}
    (α : orderedCechCochains W F p) {S : Opens X} {b c : OrderedCechIndex ι p} (h : b = c)
    (hb : S ≤ orderedCechIntersection W b) (hc : S ≤ orderedCechIntersection W c) :
    F.presheaf.map (homOfLE hb).op (α b) = F.presheaf.map (homOfLE hc).op (α c) := by
  subst h
  rfl

theorem map_map (F : X.Sheaf AddCommGrpCat.{u}) {S T R : Opens X} (h₁ : S ≤ T) (h₂ : T ≤ R)
    (x : F.presheaf.obj (op R)) :
    F.presheaf.map (homOfLE h₁).op (F.presheaf.map (homOfLE h₂).op x) =
      F.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  rfl

theorem map_self (F : X.Sheaf AddCommGrpCat.{u}) {S : Opens X} (h : S ≤ S)
    (x : F.presheaf.obj (op S)) : F.presheaf.map (homOfLE h).op x = x := by
  change F.presheaf.map (𝟙 _) x = x
  rw [F.presheaf.map_id]
  rfl

/-- The increasing one-term tuple `(j)`. -/
def singleIdx (j : ι) : OrderedCechIndex ι 0 :=
  ⟨fun _ ↦ j, fun a b hab ↦ absurd hab (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; exact lt_irrefl 0)⟩

section Homotopy

open OrderedCechIndex

variable (F : X.Sheaf AddCommGrpCat.{u}) {W : ι → Opens X} {T : Opens X}
  (hW : ∀ i, W i ≤ T) {j : ι} (hj : T ≤ W j)

include hW in
theorem intersection_le_bound {p : ℕ} (a : OrderedCechIndex ι p) :
    orderedCechIntersection W a ≤ T :=
  iInf_le_of_le 0 (hW _)

include hW hj in
theorem intersection_le_insert {p : ℕ} (a : OrderedCechIndex ι p) (h : j ∉ Set.range a.1) :
    orderedCechIntersection W a ≤ orderedCechIntersection W (insertIdx j a h) := by
  refine le_iInf fun k ↦ ?_
  have hk : (insertIdx j a h).1 k ∈ Set.range (insertIdx j a h).1 := ⟨k, rfl⟩
  rw [range_insert] at hk
  rcases hk with hk | ⟨i, hi⟩
  · rw [hk]
    exact (intersection_le_bound hW a).trans hj
  · rw [← hi]
    exact iInf_le _ i

include hj in
theorem bound_le_singleIdx : T ≤ orderedCechIntersection W (singleIdx j) :=
  le_iInf fun _ ↦ hj

/-- Restriction of a section over `T` to every intersection of the cover. -/
def augmentationMap (s : F.presheaf.obj (op T)) : orderedCechCochains W F 0 :=
  fun a ↦ F.presheaf.map (homOfLE (intersection_le_bound hW a)).op s

/-- The degree-zero contracting map: take the component at the cover member `W j`. -/
def contractionAug (α : orderedCechCochains W F 0) : F.presheaf.obj (op T) :=
  F.presheaf.map (homOfLE (bound_le_singleIdx hj)).op (α (singleIdx j))

/-- The contracting homotopy obtained by inserting the index `j`. -/
def contraction (p : ℕ) (α : orderedCechCochains W F (p + 1)) : orderedCechCochains W F p :=
  fun a ↦ if h : j ∈ Set.range a.1 then 0 else
    ((-1 : ℤ) ^ (insertPos j a : ℕ)) •
      F.presheaf.map (homOfLE (intersection_le_insert hW hj a h)).op (α (insertIdx j a h))

theorem contractionAug_zero : contractionAug F hj (0 : orderedCechCochains W F 0) = 0 :=
  map_zero _

theorem contraction_zero (p : ℕ) :
    contraction F hW hj p (0 : orderedCechCochains W F (p + 1)) = 0 := by
  apply funext
  intro a
  unfold contraction
  split_ifs
  · rfl
  · change _ • F.presheaf.map _ 0 = 0
    rw [map_zero, smul_zero]

theorem contractionAug_augmentationMap (s : F.presheaf.obj (op T)) :
    contractionAug F hj (augmentationMap F hW s) = s := by
  unfold contractionAug augmentationMap
  rw [map_map, map_self]

theorem homotopy_succ (p : ℕ) (α : orderedCechCochains W F (p + 1)) :
    (orderedCechDifferential W F p).hom (contraction F hW hj p α) +
        contraction F hW hj (p + 1) ((orderedCechDifferential W F (p + 1)).hom α) = α := by
  apply funext
  intro a
  change (orderedCechDifferential W F p).hom (contraction F hW hj p α) a +
    contraction F hW hj (p + 1) ((orderedCechDifferential W F (p + 1)).hom α) a = α a
  rw [differential_apply]
  by_cases h : j ∈ Set.range a.1
  · obtain ⟨m, hm⟩ := h
    have hk : contraction F hW hj (p + 1) ((orderedCechDifferential W F (p + 1)).hom α) a = 0 :=
      dif_pos ⟨m, hm⟩
    rw [hk, add_zero, Finset.sum_eq_single m]
    · unfold contraction
      rw [dif_neg (not_mem_range_remove_of_eq hm), map_zsmul, map_map, smul_smul, ← pow_add,
        insertPos_remove_of_eq hm, Even.neg_one_pow ⟨m, rfl⟩, one_smul]
      rw [map_congr_index F α (insert_remove_of_eq hm) _ le_rfl, map_self]
    · intro r _ hr
      unfold contraction
      rw [dif_pos (mem_range_remove_of_ne hm hr)]
      change _ • F.presheaf.map _ 0 = 0
      rw [map_zero, smul_zero]
    · intro hm'
      exact absurd (Finset.mem_univ m) hm'
  · have hle : ∀ r : Fin (p + 2), orderedCechIntersection W a ≤
        orderedCechIntersection W (insertIdx j (a.remove r) (not_mem_range_remove h r)) :=
      fun r ↦ (intersection_le_remove W a r).trans (intersection_le_insert hW hj _ _)
    have hdk : ∀ r : Fin (p + 2),
        ((-1 : ℤ) ^ (r : ℕ)) • F.presheaf.map (homOfLE (intersection_le_remove W a r)).op
          (contraction F hW hj p α (a.remove r)) =
        ((-1 : ℤ) ^ ((r : ℕ) + insertPos j (a.remove r))) •
          F.presheaf.map (homOfLE (hle r)).op
            (α (insertIdx j (a.remove r) (not_mem_range_remove h r))) := by
      intro r
      unfold contraction
      rw [dif_neg (not_mem_range_remove h r), map_zsmul, map_map, smul_smul, ← pow_add]
    have hkd : contraction F hW hj (p + 1) ((orderedCechDifferential W F (p + 1)).hom α) a =
        α a + ∑ r : Fin (p + 2), -(((-1 : ℤ) ^ ((r : ℕ) + insertPos j (a.remove r))) •
          F.presheaf.map (homOfLE (hle r)).op
            (α (insertIdx j (a.remove r) (not_mem_range_remove h r)))) := by
      unfold contraction
      rw [dif_neg h, differential_apply, map_sum, Finset.smul_sum,
        Fin.sum_univ_succAbove _ (insertPos j a)]
      congr 1
      · rw [map_zsmul, map_map, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul,
          map_congr_index F α (insert_remove_insertPos j a h) _ le_rfl, map_self]
      · refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [map_zsmul, map_map, smul_smul, ← pow_add, insertPos_add_succAbove j a h r,
          pow_succ, mul_neg_one, neg_smul,
          map_congr_index F α (insert_remove_succAbove j a h r) _ (hle r)]
    rw [Finset.sum_congr rfl fun r _ ↦ hdk r, hkd, Finset.sum_neg_distrib]
    abel

theorem homotopy_zero (α : orderedCechCochains W F 0) :
    augmentationMap F hW (contractionAug F hj α) +
        contraction F hW hj 0 ((orderedCechDifferential W F 0).hom α) = α := by
  apply funext
  intro a
  change augmentationMap F hW (contractionAug F hj α) a +
    contraction F hW hj 0 ((orderedCechDifferential W F 0).hom α) a = α a
  unfold augmentationMap contractionAug
  rw [map_map]
  by_cases h : j ∈ Set.range a.1
  · obtain ⟨m, hm⟩ := h
    have ha : singleIdx j = a := by
      apply Subtype.ext
      funext k
      rw [Fin.fin_one_eq_zero k, ← hm, Fin.fin_one_eq_zero m]
      rfl
    have hk : contraction F hW hj 0 ((orderedCechDifferential W F 0).hom α) a = 0 :=
      dif_pos ⟨m, hm⟩
    rw [hk, add_zero, map_congr_index F α ha _ le_rfl, map_self]
  · unfold contraction
    rw [dif_neg h, differential_apply, map_sum, Finset.smul_sum,
      Fin.sum_univ_succAbove _ (insertPos j a), Fin.sum_univ_one]
    rw [map_zsmul, map_map, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul,
      map_congr_index F α (insert_remove_insertPos j a h) _ le_rfl, map_self]
    rw [map_zsmul, map_map, smul_smul, ← pow_add, insertPos_add_succAbove_zero, pow_one,
      neg_one_smul, map_congr_index F α (insert_remove_succAbove_zero j a h) _
        ((intersection_le_bound hW a).trans (bound_le_singleIdx hj))]
    have hP := (intersection_le_bound hW a).trans (bound_le_singleIdx hj)
    change F.presheaf.map (homOfLE hP).op (α (singleIdx j)) +
      (α a + -F.presheaf.map (homOfLE hP).op (α (singleIdx j))) = α a
    abel

end Homotopy

/-- **Hartshorne III, Lemma 4.2.** For an open cover `U` of `X` and an abelian sheaf `F`, the
augmented sheafified Cech complex `0 → F → 𝒞^0(U, F) → 𝒞^1(U, F) → ⋯` is exact in every degree. -/
theorem augmentedSheafifiedCechComplex_exactAt (U : ι → Opens X) (hU : IsOpenCover U)
    (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (augmentedSheafifiedCechComplex U F).ExactAt n := by
  rcases n with _ | _ | p
  · rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero
      (CochainComplex.next ℕ 0)]
    apply shortComplex_exact_of_local
    intro x
    obtain ⟨j, hj⟩ := hU.exists_mem x
    refine ⟨U j, hj, fun V hV b hb ↦ ⟨0, ?_⟩⟩
    have hW : ∀ i, V ⊓ U i ≤ V := fun _ ↦ inf_le_left
    have hjV : V ≤ V ⊓ U j := le_inf le_rfl hV
    change augmentationMap F hW b = 0 at hb
    rw [map_zero]
    exact ((contractionAug_augmentationMap F hW hjV b).symm.trans
      ((congrArg (contractionAug F (W := fun i ↦ V ⊓ U i) hjV) hb).trans
        (contractionAug_zero F (W := fun i ↦ V ⊓ U i) hjV))).symm
  · rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (CochainComplex.prev_nat_succ 0)
      (CochainComplex.next ℕ 1)]
    apply shortComplex_exact_of_local
    intro x
    obtain ⟨j, hj⟩ := hU.exists_mem x
    refine ⟨U j, hj, fun V hV b hb ↦ ?_⟩
    have hW : ∀ i, V ⊓ U i ≤ V := fun _ ↦ inf_le_left
    have hjV : V ≤ V ⊓ U j := le_inf le_rfl hV
    change (orderedCechDifferential (fun i ↦ V ⊓ U i) F 0).hom b = 0 at hb
    refine ⟨contractionAug F (W := fun i ↦ V ⊓ U i) hjV b, ?_⟩
    change augmentationMap F hW (contractionAug F (W := fun i ↦ V ⊓ U i) hjV b) = b
    have h := homotopy_zero F hW hjV b
    rw [hb, contraction_zero, add_zero] at h
    exact h
  · rw [HomologicalComplex.exactAt_iff' _ (p + 1) (p + 2) (p + 3)
      (CochainComplex.prev_nat_succ (p + 1)) (CochainComplex.next ℕ (p + 2))]
    apply shortComplex_exact_of_local
    intro x
    obtain ⟨j, hj⟩ := hU.exists_mem x
    refine ⟨U j, hj, fun V hV b hb ↦ ?_⟩
    have hW : ∀ i, V ⊓ U i ≤ V := fun _ ↦ inf_le_left
    have hjV : V ≤ V ⊓ U j := le_inf le_rfl hV
    have eg : (augmentedSheafifiedCechComplex U F).d (p + 2) (p + 3) =
        cochainDifferential U F (p + 1) :=
      (CochainComplex.augment_d_succ_succ _ _ _ (p + 1) (p + 2)).trans
        (sheafifiedCechComplex_d U F (p + 1))
    have ef : (augmentedSheafifiedCechComplex U F).d (p + 1) (p + 2) =
        cochainDifferential U F p :=
      (CochainComplex.augment_d_succ_succ _ _ _ p (p + 1)).trans (sheafifiedCechComplex_d U F p)
    have hb' := (congrArg (fun φ ↦ φ.hom.app (op V) b) eg).symm.trans hb
    change (orderedCechDifferential (fun i ↦ V ⊓ U i) F (p + 1)).hom b = 0 at hb'
    refine ⟨contraction F hW hjV p b, ?_⟩
    refine (congrArg (fun φ ↦ φ.hom.app (op V) (contraction F hW hjV p b)) ef).trans ?_
    change (orderedCechDifferential (fun i ↦ V ⊓ U i) F p).hom (contraction F hW hjV p b) = b
    have h := homotopy_succ F hW hjV p b
    rw [hb', contraction_zero, add_zero] at h
    exact h


section Naturality

/-! ### Naturality in the sheaf -/

theorem refineCochains_naturality {U U' : ι → Opens X} (h : ∀ i, U' i ≤ U i)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (p : ℕ) :
    refineCochains h F p ≫ orderedCechCochainsMap U' f p =
      orderedCechCochainsMap U f p ≫ refineCochains h G p := by
  ext s
  apply funext
  intro a
  change f.hom.app _ (F.presheaf.map _ (s a)) = G.presheaf.map _ (f.hom.app _ (s a))
  exact ConcreteCategory.congr_hom (f.hom.naturality (homOfLE (intersection_mono h a)).op) (s a)

/-- A morphism of sheaves `F ⟶ G` induces `𝒞^p(U, F) ⟶ 𝒞^p(U, G)`; over `V` it acts
componentwise on the ordered Cech cochains of the cover `(V ∩ U_i)`. -/
def cochainSheafMap (U : ι → Opens X) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (p : ℕ) :
    cochainSheaf U F p ⟶ cochainSheaf U G p :=
  ObjectProperty.homMk
    { app := fun V ↦ orderedCechCochainsMap (fun i ↦ V.unop ⊓ U i) f p
      naturality := fun _ _ g ↦
        refineCochains_naturality (fun i ↦ inf_le_inf_right (U i) g.unop.le) f p }

@[simp]
theorem cochainSheafMap_id (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    cochainSheafMap U (𝟙 F) p = 𝟙 _ := by
  apply Sheaf.hom_ext
  ext V s
  rfl

@[simp, reassoc]
theorem cochainSheafMap_comp (U : ι → Opens X) {F G H : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) (g : G ⟶ H) (p : ℕ) :
    cochainSheafMap U (f ≫ g) p = cochainSheafMap U f p ≫ cochainSheafMap U g p := by
  apply Sheaf.hom_ext
  ext V s
  rfl

/-- The differentials of `𝒞^•(U, -)` commute with the maps induced by a morphism of sheaves. -/
@[reassoc]
theorem cochainSheafMap_comp_cochainDifferential (U : ι → Opens X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (p : ℕ) :
    cochainSheafMap U f p ≫ cochainDifferential U G p =
      cochainDifferential U F p ≫ cochainSheafMap U f (p + 1) := by
  apply Sheaf.hom_ext
  ext V : 2
  exact orderedCechDifferential_naturality _ f p

/-- **Naturality of the augmentation.** For a morphism of sheaves `f : F ⟶ G`, the augmentations
`F → 𝒞^0(U, F)` and `G → 𝒞^0(U, G)` commute with `f` and the induced map on `𝒞^0`. -/
@[reassoc]
theorem augmentation_naturality (U : ι → Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) :
    f ≫ augmentation U G = augmentation U F ≫ cochainSheafMap U f 0 := by
  apply Sheaf.hom_ext
  ext V s
  apply funext
  intro a
  change G.presheaf.map _ (f.hom.app V s) = f.hom.app _ (F.presheaf.map _ s)
  exact (ConcreteCategory.congr_hom (f.hom.naturality _) s).symm

/-- A morphism of sheaves induces a morphism of sheafified Cech complexes. -/
def sheafifiedCechComplexMap (U : ι → Opens X) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    sheafifiedCechComplex U F ⟶ sheafifiedCechComplex U G :=
  CochainComplex.ofHom (cochainSheafMap U f) fun p ↦ by
    rw [sheafifiedCechComplex_d, sheafifiedCechComplex_d]
    exact cochainSheafMap_comp_cochainDifferential U f p

@[simp]
theorem sheafifiedCechComplexMap_f (U : ι → Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) (p : ℕ) : (sheafifiedCechComplexMap U f).f p = cochainSheafMap U f p :=
  rfl

/-- The sheafified Cech complex `𝒞^•(U, -)`, functorial in the sheaf. -/
def sheafifiedCechComplexFunctor (U : ι → Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ where
  obj F := sheafifiedCechComplex U F
  map f := sheafifiedCechComplexMap U f
  map_id F := by
    ext p : 1
    exact cochainSheafMap_id U F p
  map_comp f g := by
    ext p : 1
    exact cochainSheafMap_comp U f g p

/-- The augmentation as a morphism of complexes from `F`, placed in degree zero, to
`𝒞^•(U, F)`. -/
def augmentationHom (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    (CochainComplex.single₀ (X.Sheaf AddCommGrpCat.{u})).obj F ⟶ sheafifiedCechComplex U F :=
  (CochainComplex.fromSingle₀Equiv _ F).symm ⟨augmentation U F, augmentation_comp_d U F⟩

@[simp]
theorem augmentationHom_f_zero (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) :
    (augmentationHom U F).f 0 = augmentation U F :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- **Naturality of the resolution.** The augmentations `F → 𝒞^•(U, F)` form a natural
transformation from the functor placing a sheaf in degree zero to `𝒞^•(U, -)`. -/
def augmentationNatTrans (U : ι → Opens X) :
    CochainComplex.single₀ (X.Sheaf AddCommGrpCat.{u}) ⟶ sheafifiedCechComplexFunctor U where
  app F := augmentationHom U F
  naturality F G f := by
    refine HomologicalComplex.from_single_hom_ext ?_
    change ((CochainComplex.single₀ _).map f).f 0 ≫ (augmentationHom U G).f 0 =
      (augmentationHom U F).f 0 ≫ cochainSheafMap U f 0
    rw [CochainComplex.single₀_map_f_zero, augmentationHom_f_zero, augmentationHom_f_zero]
    exact augmentation_naturality U f

/-- A morphism of sheaves induces a morphism of augmented sheafified Cech complexes
`0 → F → 𝒞^•(U, F)`. -/
def augmentedSheafifiedCechComplexMap (U : ι → Opens X) {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) : augmentedSheafifiedCechComplex U F ⟶ augmentedSheafifiedCechComplex U G where
  f
    | 0 => f
    | p + 1 => cochainSheafMap U f p
  comm' := by
    rintro i j (rfl : i + 1 = j)
    rcases i with _ | p
    · exact augmentation_naturality U f
    · change cochainSheafMap U f p ≫ (sheafifiedCechComplex U G).d p (p + 1) =
        (sheafifiedCechComplex U F).d p (p + 1) ≫ cochainSheafMap U f (p + 1)
      rw [sheafifiedCechComplex_d, sheafifiedCechComplex_d]
      exact cochainSheafMap_comp_cochainDifferential U f p

/-- The augmented sheafified Cech complex `0 → F → 𝒞^•(U, F)`, functorial in the sheaf. -/
def augmentedSheafifiedCechComplexFunctor (U : ι → Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ where
  obj F := augmentedSheafifiedCechComplex U F
  map f := augmentedSheafifiedCechComplexMap U f
  map_id F := by
    ext (_ | p) : 1
    · rfl
    · exact cochainSheafMap_id U F p
  map_comp f g := by
    ext (_ | p) : 1
    · rfl
    · exact cochainSheafMap_comp U f g p

/-- **Global sections of the sheafified Cech complex, naturally in the sheaf.** The isomorphisms
`Γ(X, 𝒞^•(U, F)) ≅ C^•(U, F)` form a natural isomorphism of functors to complexes. -/
def globalSectionsNatIso (U : ι → Opens X) :
    sheafifiedCechComplexFunctor U ⋙
        (globalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      orderedCechComplexFunctor U :=
  NatIso.ofComponents (fun F ↦ globalSectionsIso U F) fun f ↦ by
    ext p : 1
    exact (refineCochains_naturality (U := fun i ↦ ⊤ ⊓ U i) (fun _ ↦ le_inf le_top le_rfl)
      f p).symm

/-- **Hartshorne III, Lemma 4.2, as a resolution.** For an open cover `U` of `X`, the
augmentation `F → 𝒞^•(U, F)` is a quasi-isomorphism from `F` placed in degree zero. -/
theorem quasiIso_augmentationHom (U : ι → Opens X) (hU : IsOpenCover U)
    (F : X.Sheaf AddCommGrpCat.{u}) : QuasiIso (augmentationHom U F) := by
  have hex := augmentedSheafifiedCechComplex_exactAt U hU F
  rw [quasiIso_iff]
  intro n
  rcases n with _ | n
  · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · have h1 := hex 1
      rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (CochainComplex.prev_nat_succ 0)
        (CochainComplex.next ℕ 1)] at h1
      have h0 := hex 0
      rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero
        (CochainComplex.next ℕ 0), ShortComplex.exact_iff_mono _
        ((augmentedSheafifiedCechComplex U F).shape 0 0 (by simp))] at h0
      simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, augmentationHom_f_zero]
      exact ⟨h1, h0⟩
    all_goals rfl
  · rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj F n)]
    have h := hex (n + 2)
    rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3)
      (CochainComplex.prev_nat_succ (n + 1)) (CochainComplex.next ℕ (n + 2))] at h
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))]
    exact h

end Naturality

end SheafifiedCech

end Hartshorne
