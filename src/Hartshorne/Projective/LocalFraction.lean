/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.GlobalLocalIntersection
import Hartshorne.Projective.CanonicalRational

/-!
# Homogeneous fractions in projective local rings

The local-membership criterion used in Hartshorne, *Algebraic Geometry*, I.6,
Lemma 6.4 (p. 41).
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

universe u v

variable {k : Type u} [Field k] {σ : Type v}
  {Y : Set (ProjectiveSpace k σ)}

/-- The function-field class represented by a quotient of homogeneous forms. -/
noncomputable def projRatClass (hY : IsQuasiProjVariety Y) {n : ℕ}
    {g h : MvPolynomial σ k} (hg : g.IsHomogeneous n) (hh : h.IsHomogeneous n)
    (hne : ∃ P ∈ Y, eval P.rep h ≠ 0) :
    (Variety.ofQuasiProjective hY).FunctionField :=
  Quotient.mk _ (projRatOfFraction hY hg hh hne)

/-- A homogeneous fraction with numerator nonzero at `P` belongs to the local
ring at `P` exactly when its denominator is nonzero there. -/
theorem projRatClass_mem_localRingRange_iff
    (hY : IsQuasiProjVariety Y)
    (P : (Variety.ofQuasiProjective hY).carrier) {n : ℕ}
    {g h : MvPolynomial σ k} (hg : g.IsHomogeneous n) (hh : h.IsHomogeneous n)
    (hne : ∃ R ∈ Y, eval R.rep h ≠ 0)
    (hgP : ¬ HomogeneousVanish g P.1) :
    projRatClass hY hg hh hne ∈
        (Variety.ofQuasiProjective hY).localRingRange P ↔
      ¬ HomogeneousVanish h P.1 := by
  let q := projRatOfFraction hY hg hh hne
  constructor
  · rintro ⟨a, ha⟩
    refine Quotient.inductionOn a (motive := fun a =>
      (Variety.ofQuasiProjective hY).localToFunctionFieldAlgHom P a =
          projRatClass hY hg hh hne →
        ¬ HomogeneousVanish h P.1) ?_ ha
    intro r hrq hhP
    change eval P.1.rep h = 0 at hhP
    change eval P.1.rep g ≠ 0 at hgP
    have hrel : r.toRationalRep.Rel q := Quotient.exact hrq
    obtain ⟨W, hWopen, hPW, d, a, b, haHom, hbHom, hbne, hratio⟩ :=
      r.regular ⟨P, r.mem_U⟩
    let D : Set r.U := {x | eval x.1.1.rep h ≠ 0}
    have hDopen : IsOpen D :=
      (isOpen_projNonvanishing hh).preimage (by fun_prop)
    have hDne : D.Nonempty := by
      obtain ⟨x, hxr, hxq⟩ := Variety.opens_inter_nonempty
        (U := r.U) (V := q.U) ⟨P, r.mem_U⟩ q.nonempty_U
      exact ⟨⟨x, hxr⟩, hxq⟩
    have hpre : IsPreirreducible (Set.univ : Set r.U) :=
      Variety.preirreducible_univ r.U
    have hWDne : (W ∩ D).Nonempty := by
      obtain ⟨x, hx⟩ := hDne
      obtain ⟨z, -, hz⟩ := hpre W D hWopen hDopen
        ⟨⟨P, r.mem_U⟩, Set.mem_univ _, hPW⟩
        ⟨x, Set.mem_univ _, hx⟩
      exact ⟨z, hz⟩
    let F : MvPolynomial σ k := a * h - g * b
    have hFhom : F.IsHomogeneous (d + n) :=
      (haHom.mul hh).sub (by simpa [Nat.add_comm] using hg.mul hbHom)
    let C : Set r.U := {x | HomogeneousVanish F x.1.1}
    have hCclosed : IsClosed C := by
      have hFset : IsHomogeneousSet ({F} : Set (MvPolynomial σ k)) := by
        intro f hf
        simpa only [Set.mem_singleton_iff] using ⟨d + n, hf ▸ hFhom⟩
      have hset : C = (fun x : r.U => x.1.1) ⁻¹' projZeroSet {F} := by
        ext x
        simp [C, projZeroSet]
      rw [hset]
      exact (isClosed_projZeroSet_of_isHomogeneousSet hFset).preimage
        (by fun_prop)
    have hWDC : W ∩ D ⊆ C := by
      intro x hx
      have hcross : eval x.1.1.rep a * eval x.1.1.rep h =
          eval x.1.1.rep g * eval x.1.1.rep b := by
        apply (div_eq_div_iff (hbne x hx.1) hx.2).mp
        exact (hratio x hx.1).symm.trans (hrel x.1 x.2 hx.2)
      change eval x.1.1.rep F = 0
      simp only [F, map_sub, map_mul, sub_eq_zero]
      exact hcross
    have hWDdense : Dense (W ∩ D) := by
      rw [dense_iff_inter_open]
      intro T hT hTne
      obtain ⟨t, ht⟩ := hTne
      obtain ⟨w, hw⟩ := hWDne
      obtain ⟨z, -, hz⟩ := hpre T (W ∩ D) hT
        (hWopen.inter hDopen)
        ⟨t, Set.mem_univ _, ht⟩ ⟨w, Set.mem_univ _, hw⟩
      exact ⟨z, hz⟩
    have hPC : (⟨P, r.mem_U⟩ : r.U) ∈ C := by
      have : Set.univ ⊆ C := by
        intro x _
        exact closure_minimal hWDC hCclosed (hWDdense x)
      exact this (Set.mem_univ _)
    have hbP := hbne ⟨P, r.mem_U⟩ hPW
    have hzero : eval P.1.rep g * eval P.1.rep b = 0 := by
      change eval P.1.rep F = 0 at hPC
      simpa only [F, map_sub, map_mul, hhP, mul_zero, zero_sub, neg_eq_zero]
        using hPC
    exact (mul_ne_zero hgP hbP) hzero
  · intro hhP
    change eval P.1.rep h ≠ 0 at hhP
    let q := projRatOfFraction hY hg hh hne
    let r : Variety.GermRep (Variety.ofQuasiProjective hY) P :=
      { U := q.U
        mem_U := hhP
        toFun := q.toFun
        regular := q.regular }
    refine ⟨Quotient.mk _ r, ?_⟩
    apply Quotient.sound
    intro x hx hx'
    rfl

end Hartshorne
