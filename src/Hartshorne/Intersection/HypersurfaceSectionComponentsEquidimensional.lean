/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ProjectiveCodimensionOne
import Hartshorne.Intersection.ProjectiveDimensionTheorem

/-!
# Equidimensionality of proper hypersurface sections

Hartshorne, *Algebraic Geometry*, I.7, proof of Theorem 7.7 (p. 53), using
Theorem 7.2.

Every irreducible component of a proper hypersurface section of a positive-
dimensional projective variety has dimension exactly one less than the variety.
-/

namespace Hartshorne

open MvPolynomial Set TopologicalSpace Topology

noncomputable section

universe u

private theorem topologicalKrullDim_eq_height_of_irreducible_closed
    {X : Type*} [TopologicalSpace X] {Y : Set X}
    (hirr : IsIrreducible Y) (hclosed : IsClosed Y) :
    topologicalKrullDim Y =
      (Order.height
        (⟨Y, hirr, hclosed⟩ : IrreducibleCloseds X) : WithBot ℕ∞) := by
  rw [topologicalKrullDim_subtype_eq hclosed]
  change Order.krullDim
      (Set.Iic (⟨Y, hirr, hclosed⟩ : IrreducibleCloseds X)) = _
  rw [← Order.height_eq_krullDim_Iic]

/-- A proper closed subset of an irreducible projective algebraic set has
strictly smaller dimension. -/
private theorem projDim_lt_of_closed_ssubset_isProjVariety
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type} [Finite σ] [Nonempty σ]
    {Y Z : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y)
    (hZ : IsClosed Z) (hZY : Z ⊂ Y) : projDim Z < projDim Y := by
  classical
  let VY : IrreducibleCloseds (ProjectiveSpace k σ) := ⟨Y, hY.1, hY.2⟩
  have hdimY : projDim Y = (Order.height VY : WithBot ℕ∞) := by
    rw [projDim_def,
      topologicalKrullDim_eq_height_of_irreducible_closed hY.1 hY.2]
  obtain ⟨i⟩ := ‹Nonempty σ›
  have hYle : projDim Y ≤
      projDim (Set.univ : Set (ProjectiveSpace k σ)) :=
    (Topology.IsEmbedding.inclusion
      (Set.subset_univ Y)).isInducing.topologicalKrullDim_le
  have hheight_ne_top : Order.height VY ≠ ⊤ := by
    have hdimfin : projDim Y < ⊤ := hYle.trans_lt <| by
      rw [projDim_univ (k := k) i]
      exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)
    rw [hdimY] at hdimfin
    intro htop
    rw [htop] at hdimfin
    exact (lt_irrefl _ hdimfin)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hheight_ne_top
  have hm' : Order.height VY = m := hm.symm
  change topologicalKrullDim Z < projDim Y
  rw [topologicalKrullDim_subtype_eq hZ, hdimY, hm']
  change Order.krullDim
    {T : IrreducibleCloseds (ProjectiveSpace k σ) // (T : Set _) ⊆ Z} <
      (m : WithBot ℕ∞)
  rw [Order.krullDim_lt_coe_iff]
  intro p
  let q : LTSeries (IrreducibleCloseds (ProjectiveSpace k σ)) :=
    p.map (fun T => T.1) (fun _ _ h => h)
  have hqY : q.last < VY := by
    change ((q.last : IrreducibleCloseds (ProjectiveSpace k σ)) : Set _) ⊂ Y
    exact Set.ssubset_of_subset_of_ssubset p.last.2 hZY
  have hlen := Order.length_le_height_last (p := q.snoc VY hqY)
  have hlenV : ((q.snoc VY hqY).length : ℕ∞) ≤ Order.height VY := by
    simpa using hlen
  rw [hm'] at hlenV
  have hlen' : p.length + 1 ≤ m := by
    simp [q] at hlenV
    exact_mod_cast hlenV
  omega

/-- The dimension of a projective variety is represented by a natural
number. -/
private theorem exists_projDim_eq_nat_of_isProjVariety
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type} [Finite σ] [Nonempty σ]
    {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y) :
    ∃ r : ℕ, projDim Y = (r : WithBot ℕ∞) := by
  classical
  obtain ⟨P, hPY⟩ := hY.1.nonempty
  obtain ⟨i, hi⟩ := exists_mem_standardChart P
  have hne : (Y ∩ standardChart i).Nonempty := ⟨P, hPY, hi⟩
  have hA : IsAffineVariety (chartMap i '' (Y ∩ standardChart i)) :=
    isAffineVariety_chartMap_image i hY hne
  letI : IsDomain (coordinateRing (chartMap i '' (Y ∩ standardChart i))) :=
    isDomain_coordinateRing hA
  obtain ⟨r, hr⟩ := exists_ringKrullDim_eq_natCast k
    (coordinateRing (chartMap i '' (Y ∩ standardChart i)))
  refine ⟨r, ?_⟩
  rw [projDim_eq_dim_chart hY i hne,
    dim_eq_ringKrullDim_coordinateRing hA.isAlgebraicSet, hr]

/-- **Equidimensionality in the proof of Theorem I.7.7.** Every irreducible
component of a proper positive-degree hypersurface section of a projective
variety of dimension `r > 0` has projective dimension `r - 1`. -/
theorem projectiveHypersurfaceSectionComponent_projDim_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {n r d : ℕ} (hn : 0 < n) (hr : 0 < r) (hd : 0 < d)
    {Y : Set (ProjectiveSpace k (Fin (n + 1)))} (hY : IsProjVariety Y)
    (hYdim : projDim Y = (r : WithBot ℕ∞))
    (f : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
    (hfirr : Irreducible f)
    (hproper : ¬Y ⊆ projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k)))
    (W : irreducibleComponents
      ↥(Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k)))) :
    projDim (projectiveComponentCarrier W.1) =
      ((r - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  let H : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  let I : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span {f}
  have hIhom : IsHomogeneousIdeal I :=
    Ideal.homogeneous_span _ _ fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      subst g
      exact isHomogeneousElem_iff.mpr ⟨d, hf⟩
  have hIprime : I.IsPrime :=
    (Ideal.span_singleton_prime hfirr.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hfirr)
  have hZI : projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k)) = H := by
    exact projZeroSet_span _
  obtain ⟨w, hwW⟩ := W.2.1.nonempty
  have hHne : H.Nonempty := ⟨w.1, w.2.2⟩
  have hIne :
      (projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
    rw [hZI]
    exact hHne
  have hHalg : IsProjAlgebraicSet H := by
    refine ⟨{f}, ?_, rfl⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    exact ⟨d, hf⟩
  have hH : IsProjVariety H := by
    refine ⟨(isIrreducible_iff_isPrime_homogeneousVanishingIdeal hHalg).mpr ?_,
      isClosed_iff_isProjAlgebraicSet.mpr hHalg⟩
    rw [← hZI]
    rw [homogeneousVanishingIdeal_projZeroSet hIhom hIne, hIprime.radical]
    exact hIprime
  have hHdim : projDim H = ((n - 1 : ℕ) : WithBot ℕ∞) :=
    (projective_codimension_one_iff_hypersurface hH hn).2
      ⟨f, d, hd, hf, hfirr, rfl⟩
  have hInterClosed : IsClosed (Y ∩ H) := hY.2.inter hH.2
  have hWvar : IsProjVariety (projectiveComponentCarrier W.1) :=
    isProjVariety_projectiveComponentCarrier hInterClosed W
  obtain ⟨m, hWdim⟩ := exists_projDim_eq_nat_of_isProjVariety hWvar
  have hlower := projective_dimension_theorem hY hH W
  rw [hYdim, hHdim, hWdim, Nat.card_fin] at hlower
  have hlowerNat : r + (n - 1) ≤ m + n := by
    exact_mod_cast hlower
  have hrm : r - 1 ≤ m := by omega
  have hWsubInter : projectiveComponentCarrier W.1 ⊆ Y ∩ H := by
    rintro _ ⟨z, hzW, rfl⟩
    exact z.2
  have hWsubY : projectiveComponentCarrier W.1 ⊆ Y :=
    hWsubInter.trans Set.inter_subset_left
  have hWssubY : projectiveComponentCarrier W.1 ⊂ Y := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hWsubY, ?_⟩
    intro hWY
    apply hproper
    intro P hPY
    have hPW : P ∈ projectiveComponentCarrier W.1 := by
      rw [hWY]
      exact hPY
    exact (hWsubInter hPW).2
  have hupper :=
    projDim_lt_of_closed_ssubset_isProjVariety hY hWvar.2 hWssubY
  rw [hYdim, hWdim] at hupper
  have hmr : m < r := by
    exact_mod_cast hupper
  have hmr' : m ≤ r - 1 := by omega
  rw [hWdim]
  norm_cast
  exact le_antisymm hmr' hrm

end

end Hartshorne
