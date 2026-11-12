/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SheafAlgebraOperations

/-!
# Sections of a graded sheafification over quasi-compact opens

Supplements Hartshorne II.7 (p. 160, condition (†): a quasi-coherent sheaf of graded algebras is
`S = ⊕_{d ≥ 0} S_d`). Let `(X, 𝒪_X)` be a ringed space and let `P` be a presheaf of
`𝒪_X`-algebras graded by subpresheaves `C r → P` (`PresheafAlgebra.IsGraded`). Its sheafification
`aP` is the direct sum of the sheafifications `a(C r)` in the category of `𝒪_X`-modules
(`PresheafAlgebra.IsGraded.isColimit`). Here we show that over a quasi-compact open `U` the
sections are the direct sum of the sections of the components:
`Γ(U, aP) = ⊕_r Γ(U, a(C r))` (`PresheafAlgebra.IsGraded.isInternal_sections`).

The projections `aP → a(C r)` (`PresheafAlgebra.IsGraded.sheafProj`) are the sheafifications of
the projections of the presheaf direct sum; every section of `aP` is locally the image of a section
of `P`, which has finitely many nonzero components, and quasi-compactness bounds the degrees that
occur.
-/

universe u

open CategoryTheory TopologicalSpace Opposite Limits

namespace Hartshorne

namespace SheafAlgebraOperations

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} {S : PresheafAlgebra P}
  {C : ℕ → PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} {ι : ∀ r, C r ⟶ P}

namespace PresheafAlgebra.IsGraded

/-- The Kronecker family `C t ⟶ C r`: the identity for `t = r` and zero otherwise. -/
private noncomputable def delta (r : ℕ) (t : ℕ) : C t ⟶ C r :=
  if h : t = r then eqToHom (congrArg C h) else 0

variable (hS : S.IsGraded C ι)
include hS

/-- The projection `P ⟶ C r` of the presheaf direct sum onto its component of degree `r`. -/
noncomputable def presheafProj (r : ℕ) : P ⟶ C r :=
  Cofan.IsColimit.desc hS.isColimitPresheaf (delta r)

/-- The projection `aP ⟶ a(C r)` of the sheafification onto its component of degree `r`. -/
noncomputable def sheafProj (r : ℕ) : sheafify P ⟶ sheafify (C r) :=
  sheafifyMap (hS.presheafProj r)

private lemma sheafifyMap_ι_sheafProj (t r : ℕ) :
    sheafifyMap (ι t) ≫ hS.sheafProj r = sheafifyMap (delta (C := C) r t) := by
  rw [sheafProj, ← Functor.map_comp]
  congr 1
  exact Cofan.IsColimit.fac hS.isColimitPresheaf _ t

/-- The projection onto degree `r` is a left inverse of the inclusion of degree `r`. -/
lemma sheafProj_ι_self (r : ℕ) (U : (Opens X)ᵒᵖ) (a : (sheafify (C r)).val.obj U) :
    (hS.sheafProj r).val.app U ((sheafifyMap (ι r)).val.app U a) = a := by
  have h := hS.sheafifyMap_ι_sheafProj r r
  rw [delta, dif_pos rfl, eqToHom_refl,
    show sheafifyMap (𝟙 (C r)) = 𝟙 _ from CategoryTheory.Functor.map_id _ _] at h
  exact congrArg (fun φ : sheafify (C r) ⟶ sheafify (C r) => φ.val.app U a) h

/-- The projection onto degree `r` kills the component of degree `t ≠ r`. -/
lemma sheafProj_ι_of_ne {t r : ℕ} (htr : t ≠ r) (U : (Opens X)ᵒᵖ)
    (a : (sheafify (C t)).val.obj U) :
    (hS.sheafProj r).val.app U ((sheafifyMap (ι t)).val.app U a) = 0 := by
  have : (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).IsLeftAdjoint :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).isLeftAdjoint
  have h := hS.sheafifyMap_ι_sheafProj t r
  rw [delta, dif_neg htr,
    show sheafifyMap (0 : C t ⟶ C r) = 0 from CategoryTheory.Functor.map_zero _ _ _] at h
  exact congrArg (fun φ : sheafify (C t) ⟶ sheafify (C r) => φ.val.app U a) h

/-- A section in the image of degree `r` is recovered from its component of degree `r`. -/
lemma ι_sheafProj_of_mem {r : ℕ} {U : (Opens X)ᵒᵖ} {y : (sheafify P).val.obj U}
    (hy : y ∈ LinearMap.range ((sheafifyMap (ι r)).val.app U).hom) :
    (sheafifyMap (ι r)).val.app U ((hS.sheafProj r).val.app U y) = y := by
  obtain ⟨a, rfl⟩ := hy
  exact congrArg _ (hS.sheafProj_ι_self r U a)

/-- If a section is a finite sum of homogeneous sections with degrees in `T' ⊆ T`, it is the sum
of its components of degrees in `T`. -/
private lemma sum_ι_sheafProj_of_eq_sum {U : (Opens X)ᵒᵖ} {T T' : Finset ℕ} (hT : T' ⊆ T)
    (w : ∀ t, (sheafify (C t)).val.obj U) :
    ∑ r ∈ T, (sheafifyMap (ι r)).val.app U ((hS.sheafProj r).val.app U
      (∑ t ∈ T', (sheafifyMap (ι t)).val.app U (w t))) =
      ∑ t ∈ T', (sheafifyMap (ι t)).val.app U (w t) := by
  have key : ∀ r t, (sheafifyMap (ι r)).val.app U ((hS.sheafProj r).val.app U
      ((sheafifyMap (ι t)).val.app U (w t))) =
      if r = t then (sheafifyMap (ι t)).val.app U (w t) else 0 := by
    intro r t
    split_ifs with h
    · subst h
      rw [hS.sheafProj_ι_self]
    · rw [hS.sheafProj_ι_of_ne (Ne.symm h), map_zero]
  simp_rw [map_sum, key]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t ht => by rw [Finset.sum_ite_eq' T t, if_pos (hT ht)]

/-- Every section of the sheafification is locally a finite sum of homogeneous sections. -/
private lemma exists_local_sum {U : Opens X} (s : (sheafify P).val.obj (op U)) {x : X}
    (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U) (T : Finset ℕ)
      (w : ∀ t, (sheafify (C t)).val.obj (op V)),
      (sheafify P).val.map i.op s = ∑ t ∈ T, (sheafifyMap (ι t)).val.app (op V) (w t) := by
  classical
  obtain ⟨V, hV, i, p, e⟩ := exists_unit_eq_map P s hx
  obtain ⟨d, rfl⟩ := (hS.bijective (op V)).2 p
  refine ⟨V, hV, i, d.support, fun t => (sheafifyUnit (C t)).app (op V) (d t), ?_⟩
  rw [← e]
  conv_lhs => rw [← DirectSum.sum_support_of d]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← DirectSum.lof_eq_of ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)),
    DirectSum.toModule_lof]
  exact (sheafifyMap_unit _ _ _).symm

/-- **Over a quasi-compact open, every section of the sheafification is the finite sum of its
homogeneous components.** -/
theorem exists_finset_sum_eq {U : Opens X} (hU : IsCompact (U : Set X))
    (s : (sheafify P).val.obj (op U)) :
    ∃ T : Finset ℕ, ∑ r ∈ T, (sheafifyMap (ι r)).val.app (op U)
      ((hS.sheafProj r).val.app (op U) s) = s := by
  classical
  have hloc : ∀ x : U, ∃ (V : Opens X) (_ : (x : X) ∈ V) (i : V ⟶ U) (T : Finset ℕ)
      (w : ∀ t, (sheafify (C t)).val.obj (op V)),
      (sheafify P).val.map i.op s = ∑ t ∈ T, (sheafifyMap (ι t)).val.app (op V) (w t) :=
    fun x => hS.exists_local_sum s x.2
  choose V hxV i T w hw using hloc
  obtain ⟨F, hF⟩ := hU.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxV _⟩)
  refine ⟨F.biUnion T, ?_⟩
  apply sheaf_section_ext
  intro y hy
  obtain ⟨x, hxF, hyx⟩ := Set.mem_iUnion₂.1 (hF hy)
  refine ⟨V x, hyx, i x, ?_⟩
  have hnat : ∀ r, (sheafify P).val.map (i x).op ((sheafifyMap (ι r)).val.app (op U)
      ((hS.sheafProj r).val.app (op U) s)) = (sheafifyMap (ι r)).val.app (op (V x))
      ((hS.sheafProj r).val.app (op (V x)) ((sheafify P).val.map (i x).op s)) := fun r => by
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  rw [map_sum, Finset.sum_congr rfl fun r _ => hnat r, hw x]
  exact hS.sum_ι_sheafProj_of_eq_sum (Finset.subset_biUnion_of_mem T hxF) _

/-- The projection onto degree `r` of a sum of homogeneous sections is its component of
degree `r`. -/
private lemma sheafProj_coeAddMonoidHom {U : (Opens X)ᵒᵖ} (r : ℕ)
    (f : DirectSum ℕ fun r => (LinearMap.range ((sheafifyMap (ι r)).val.app U).hom).toAddSubgroup) :
    (hS.sheafProj r).val.app U (DirectSum.coeAddMonoidHom _ f) =
      (hS.sheafProj r).val.app U (f r : (sheafify P).val.obj U) := by
  classical
  let Φ : (DirectSum ℕ fun r =>
      (LinearMap.range ((sheafifyMap (ι r)).val.app U).hom).toAddSubgroup) →+
      (sheafify (C r)).val.obj U :=
    ((hS.sheafProj r).val.app U).hom.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom _)
  let Ψ : (DirectSum ℕ fun r =>
      (LinearMap.range ((sheafifyMap (ι r)).val.app U).hom).toAddSubgroup) →+
      (sheafify (C r)).val.obj U :=
    ((hS.sheafProj r).val.app U).hom.toAddMonoidHom.comp
      ((AddSubgroup.subtype _).comp (DFinsupp.evalAddMonoidHom r))
  have : Φ = Ψ := by
    refine DirectSum.addHom_ext fun t y => ?_
    change (hS.sheafProj r).val.app U (DirectSum.coeAddMonoidHom _ (DirectSum.of (fun r =>
        (LinearMap.range ((sheafifyMap (ι r)).val.app U).hom).toAddSubgroup) t y)) =
      (hS.sheafProj r).val.app U ((DirectSum.of (fun r =>
        (LinearMap.range ((sheafifyMap (ι r)).val.app U).hom).toAddSubgroup) t y r :
          (sheafify P).val.obj U))
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : t = r
    · subst h
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), ZeroMemClass.coe_zero, map_zero]
      obtain ⟨a, ha⟩ := y.2
      rw [← ha]
      exact hS.sheafProj_ι_of_ne h U a
  exact DFunLike.congr_fun this f

/-- **Over a quasi-compact open `U`, the sections of the sheafification are the direct sum of the
sections of the homogeneous components:** `Γ(U, aP) = ⊕_r Γ(U, a(C r))`, the summands being the
images of the inclusions `Γ(U, a(C r)) → Γ(U, aP)`. -/
theorem isInternal_sections {U : Opens X} (hU : IsCompact (U : Set X)) :
    DirectSum.IsInternal fun r =>
      (LinearMap.range ((sheafifyMap (ι r)).val.app (op U)).hom).toAddSubgroup := by
  classical
  refine ⟨fun f g hfg => ?_, fun s => ?_⟩
  · ext r
    have h := congrArg ((hS.sheafProj r).val.app (op U)) hfg
    rw [hS.sheafProj_coeAddMonoidHom, hS.sheafProj_coeAddMonoidHom] at h
    rw [← hS.ι_sheafProj_of_mem (f r).2, ← hS.ι_sheafProj_of_mem (g r).2, h]
  · obtain ⟨T, hT⟩ := hS.exists_finset_sum_eq hU s
    refine ⟨∑ r ∈ T, DirectSum.of _ r ⟨_, LinearMap.mem_range_self _
      ((hS.sheafProj r).val.app (op U) s)⟩, ?_⟩
    rw [map_sum]
    exact (Finset.sum_congr rfl fun r _ => DirectSum.coeAddMonoidHom_of _ _ _).trans hT

end PresheafAlgebra.IsGraded

end SheafAlgebraOperations

end Hartshorne
