/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ProjChartDimension
import Hartshorne.Projective.Correspondence
import Hartshorne.Affine.HypersurfaceDimension
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Projective codimension-one varieties are hypersurfaces

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.8 (p. 12).

A projective variety in `P^n` has dimension `n - 1` exactly when it is cut out
by one irreducible homogeneous polynomial of positive degree.
-/

namespace Hartshorne

open MvPolynomial

universe u

variable {k : Type u} [Field k]

/-- A principal homogeneous ideal with irreducible generator admits a
homogeneous generator of positive degree. -/
private theorem exists_pos_isHomogeneous_of_irreducible_span_isHomogeneous
    {sigma : Type*} {f : MvPolynomial sigma k} (hf : Irreducible f)
    (hhom : IsHomogeneousIdeal (Ideal.span ({f} : Set (MvPolynomial sigma k)))) :
    exists d : Nat, 0 < d ∧ f.IsHomogeneous d := by
  obtain ⟨m, hm⟩ : ∃ m, coeff m f ≠ 0 := exists_coeff_ne_zero hf.ne_zero
  let d := m.degree
  let g := homogeneousComponent d f
  have hgne : g ≠ 0 := by
    intro hg
    have hcoeff := congrArg (coeff m) hg
    rw [coeff_homogeneousComponent] at hcoeff
    exact hm (by simpa [d] using hcoeff)
  have hgmem : g ∈ Ideal.span ({f} : Set (MvPolynomial sigma k)) := by
    have hcomp := (Ideal.IsHomogeneous.mem_iff (homogeneousSubmodule sigma k) hhom).1
      (Ideal.mem_span_singleton_self f) d
    rw [← DirectSum.Decomposition.decompose'_eq,
      MvPolynomial.decomposition.decompose'_apply] at hcomp
    exact hcomp
  obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton.mp hgmem)
  have hane : a ≠ 0 := by
    rintro rfl
    simp [ha] at hgne
  have hgd : g.totalDegree = d :=
    (homogeneousComponent_isHomogeneous d f).totalDegree hgne
  have hdeq : d = f.totalDegree := by
    apply le_antisymm
    · exact le_totalDegree (mem_support_iff.mpr hm)
    · have hle := totalDegree_le_of_dvd_of_isDomain
        (Ideal.mem_span_singleton.mp hgmem) hgne
      rwa [hgd] at hle
  have had : a.totalDegree = 0 := by
    have hmul := totalDegree_mul_of_isDomain hf.ne_zero hane
    rw [← ha, hgd, hdeq] at hmul
    omega
  have haC : a = C (coeff 0 a) := totalDegree_eq_zero_iff_eq_C.mp had
  have hcne : coeff 0 a ≠ 0 := by
    intro hc
    exact hane (haC.trans (by simp [hc]))
  refine ⟨d, ?_, ?_⟩
  · by_contra hd0
    have hdz : d = 0 := Nat.eq_zero_of_not_pos hd0
    have hfC : f = C (coeff 0 f) :=
      totalDegree_eq_zero_iff_eq_C.mp (hdeq.symm.trans hdz)
    have hc : coeff 0 f ≠ 0 := by
      intro hc
      exact hf.ne_zero (hfC.trans (by simp [hc]))
    exact hf.not_isUnit
      (hfC ▸ (isUnit_iff_ne_zero.mpr hc).map (C : k →+* MvPolynomial sigma k))
  · have hg : g.IsHomogeneous d := homogeneousComponent_isHomogeneous d f
    have heq : f = C (coeff 0 a)⁻¹ * g := by
      rw [haC] at ha
      rw [ha, mul_comm, mul_assoc, ← map_mul]
      simp [hcne]
    rw [heq]
    exact hg.C_mul _

variable [IsAlgClosed k]

/-- **Exercise 2.8.** A projective variety in `P^n`, for `n > 0`, has
dimension `n - 1` if and only if it is the zero set of one irreducible
homogeneous polynomial of positive degree. -/
theorem projective_codimension_one_iff_hypersurface {n : Nat}
    {Y : Set (ProjectiveSpace k (Fin (n + 1)))} (hY : IsProjVariety Y)
    (hn : 0 < n) :
    projDim Y = ((n - 1 : Nat) : WithBot ENat) ↔
      ∃ (f : MvPolynomial (Fin (n + 1)) k) (d : Nat),
        0 < d ∧ f.IsHomogeneous d ∧ Irreducible f ∧
          Y = projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k)) := by
  classical
  constructor
  · intro hdim
    let P := homogeneousVanishingIdeal Y
    haveI hprime : P.IsPrime :=
      (isIrreducible_iff_isPrime_homogeneousVanishingIdeal hY.isProjAlgebraicSet).1 hY.1
    haveI : FiniteRingKrullDim (MvPolynomial (Fin (n + 1)) k) :=
      finiteRingKrullDim_of_finiteType k (MvPolynomial (Fin (n + 1)) k)
    obtain ⟨h, hh⟩ : ∃ h : Nat, P.height = h :=
      ENat.ne_top_iff_exists.mp (P.height_ne_top hprime.ne_top) |>.imp
        fun _ e => e.symm
    have hcoord : ringKrullDim (homogeneousCoordinateRing Y) =
        (n : WithBot ENat) := by
      rw [ringKrullDim_homogeneousCoordinateRing_eq_projDim_add_one hY, hdim]
      norm_cast
      omega
    have hdimA : ringKrullDim (MvPolynomial (Fin (n + 1)) k) =
        ((n + 1 : Nat) : WithBot ENat) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field]
      simp
    have hform := height_add_ringKrullDim_quotient_eq k
      (MvPolynomial (Fin (n + 1)) k) P h hh
    have hh1 : h = 1 := by
      rw [hcoord, hdimA] at hform
      have hcast : (h : WithBot ENat) + (n : WithBot ENat) =
          ((h + n : Nat) : WithBot ENat) := by
        push_cast
        ring
      rw [hcast] at hform
      have hnat : h + n = n + 1 := by exact_mod_cast hform
      omega
    rw [hh1] at hh
    obtain ⟨f, hfP⟩ :=
      (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
    rw [Ideal.submodule_span_eq] at hfP
    have hfne : f ≠ 0 := by
      rintro rfl
      exact Ideal.ne_bot_of_height_eq_one hh (by simpa using hfP)
    have hspanprime : (Ideal.span ({f} : Set (MvPolynomial (Fin (n + 1)) k))).IsPrime := by
      rw [← hfP]
      infer_instance
    have hfirr : Irreducible f :=
      (UniqueFactorizationMonoid.irreducible_iff_prime).2
        ((Ideal.span_singleton_prime hfne).1 hspanprime)
    have hhomspan : IsHomogeneousIdeal
        (Ideal.span ({f} : Set (MvPolynomial (Fin (n + 1)) k))) := by
      rw [← hfP]
      exact isHomogeneousIdeal_homogeneousVanishingIdeal Y
    obtain ⟨d, hdpos, hfh⟩ :=
      exists_pos_isHomogeneous_of_irreducible_span_isHomogeneous hfirr hhomspan
    refine ⟨f, d, hdpos, hfh, hfirr, ?_⟩
    have hZ := hY.isProjAlgebraicSet.projZeroSet_homogeneousVanishingIdeal_eq
    rw [show homogeneousVanishingIdeal Y = Ideal.span ({f} : Set _) from hfP,
      projZeroSet_span] at hZ
    exact hZ.symm
  · rintro ⟨f, d, hdpos, hfh, hfirr, hYeq⟩
    let I : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span {f}
    have hIhom : IsHomogeneousIdeal I :=
      Ideal.homogeneous_span _ _ fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        subst g
        exact isHomogeneousElem_iff.mpr ⟨d, hfh⟩
    have hZI : projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k)) = Y := by
      rw [show I = Ideal.span ({f} : Set _) from rfl, projZeroSet_span]
      exact hYeq.symm
    have hIne : (projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
      rw [hZI]
      exact hY.1.nonempty
    haveI hIprime : I.IsPrime := by
      exact (Ideal.span_singleton_prime hfirr.ne_zero).2
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp hfirr)
    have hJ : homogeneousVanishingIdeal Y = I := by
      rw [← hZI, homogeneousVanishingIdeal_projZeroSet hIhom hIne,
        hIprime.radical]
    have hIheight : I.height = 1 := by
      exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hfirr.ne_zero)
        fun hunit => hIprime.ne_top (Ideal.span_singleton_eq_top.2 hunit)
    haveI : IsDomain (homogeneousCoordinateRing Y) :=
      isDomain_homogeneousCoordinateRing hY
    obtain ⟨s, hs⟩ := exists_ringKrullDim_eq_natCast k (homogeneousCoordinateRing Y)
    have hdimA : ringKrullDim (MvPolynomial (Fin (n + 1)) k) =
        ((n + 1 : Nat) : WithBot ENat) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field]
      simp
    have hform := height_add_ringKrullDim_quotient_eq k
      (MvPolynomial (Fin (n + 1)) k) I 1 hIheight
    have hquot : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ I) =
        (s : WithBot ENat) := by
      rw [← hJ]
      exact hs
    rw [hquot, hdimA] at hform
    have hsn : s = n := by
      have : 1 + s = n + 1 := by exact_mod_cast hform
      omega
    have hcoord := ringKrullDim_homogeneousCoordinateRing_eq_projDim_add_one hY
    rw [hs, hsn] at hcoord
    obtain ⟨P, hPY⟩ := hY.1.nonempty
    obtain ⟨i, hi⟩ := exists_mem_standardChart P
    have hne : (Y ∩ standardChart i).Nonempty := ⟨P, hPY, hi⟩
    have hA : IsAffineVariety (chartMap i '' (Y ∩ standardChart i)) :=
      isAffineVariety_chartMap_image i hY hne
    haveI : IsDomain (coordinateRing (chartMap i '' (Y ∩ standardChart i))) :=
      isDomain_coordinateRing hA
    obtain ⟨r, hr⟩ := exists_ringKrullDim_eq_natCast k
      (coordinateRing (chartMap i '' (Y ∩ standardChart i)))
    have hproj : projDim Y = (r : WithBot ENat) := by
      rw [projDim_eq_dim_chart hY i hne,
        dim_eq_ringKrullDim_coordinateRing hA.isAlgebraicSet, hr]
    rw [hproj] at hcoord
    have hrn : r + 1 = n := by exact_mod_cast hcoord.symm
    have hrpred : r = n - 1 := by omega
    rw [hproj, hrpred]

end Hartshorne
