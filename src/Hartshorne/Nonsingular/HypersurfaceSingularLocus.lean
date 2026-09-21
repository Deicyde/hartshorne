/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.HypersurfaceDimension
import Hartshorne.Nonsingular.AffineSingularLocus
import Hartshorne.Nonsingular.IrreduciblePartial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# The singular locus of an irreducible hypersurface is proper

Hartshorne, *Algebraic Geometry*, I.5, proof of Theorem 5.3 (p. 33).

An irreducible polynomial over an algebraically closed field has a nonzero
partial derivative.  That partial cannot lie in the principal ideal generated
by the polynomial, since its degree in the differentiated variable is smaller.
The Nullstellensatz therefore supplies a point of the hypersurface where the
partial does not vanish.  The one-row Jacobian has rank one there, so the point
is nonsingular.  Together with affine closedness, this makes the singular locus
a proper closed subset and the nonsingular locus a nonempty open subset.
-/

namespace Hartshorne

open MvPolynomial

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem vanishingIdeal_zeroSet_singleton_eq_span
    {n : ℕ} {f : MvPolynomial (Fin n) k} (hf : Irreducible f) :
    vanishingIdeal k (zeroSet ({f} : Set (MvPolynomial (Fin n) k))) =
      Ideal.span {f} := by
  have hfne : f ≠ 0 := hf.ne_zero
  have hprime : (Ideal.span {f}).IsPrime :=
    (Ideal.span_singleton_prime hfne).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.1 hf)
  have hspan :
      zeroSet ({f} : Set (MvPolynomial (Fin n) k)) =
        zeroSet ((Ideal.span {f} : Ideal (MvPolynomial (Fin n) k)) : Set _) := by
    rw [zeroSet_eq_zeroLocus_span, zeroLocus_eq_zeroSet]
  rw [hspan, vanishingIdeal_zeroSet_eq_radical, hprime.radical]

/-- The zero set of an irreducible polynomial is an affine variety. -/
theorem isAffineVariety_zeroSet_singleton_of_irreducible
    {n : ℕ} {f : MvPolynomial (Fin n) k} (hf : Irreducible f) :
    IsAffineVariety (zeroSet ({f} : Set (MvPolynomial (Fin n) k))) := by
  have hprime : (Ideal.span {f}).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.1 hf)
  rw [zeroSet_eq_zeroLocus_span]
  exact isAffineVariety_zeroLocus_of_isPrime hprime

omit [IsAlgClosed k] in
private theorem degreeOf_pderiv_lt
    {n : ℕ} {f : MvPolynomial (Fin n) k} {i : Fin n}
    (hderiv : pderiv i f ≠ 0) :
    degreeOf i (pderiv i f) < degreeOf i f := by
  classical
  rw [degreeOf_eq_sup]
  obtain ⟨m, hm, hmax⟩ :=
    (pderiv i f).support.exists_mem_eq_sup (by simpa) (fun m => m i)
  rw [hmax]
  have hcoeff : coeff m (pderiv i f) ≠ 0 := by
    simpa [mem_support_iff] using hm
  rw [coeff_pderiv] at hcoeff
  have hcoeff_f : coeff (m + Finsupp.single i 1) f ≠ 0 := by
    intro hzero
    exact hcoeff (by simp [hzero])
  have hmem_f : m + Finsupp.single i 1 ∈ f.support := by
    simpa [mem_support_iff] using hcoeff_f
  have hle := le_degreeOf_of_mem_support i hmem_f
  simpa using hle

private theorem exists_point_eval_pderiv_ne_zero
    {n : ℕ} {f : MvPolynomial (Fin n) k} (hf : Irreducible f) :
    ∃ (P : zeroSet ({f} : Set (MvPolynomial (Fin n) k))) (i : Fin n),
      eval (P : Fin n → k) (pderiv i f) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_pderiv_ne_zero_of_irreducible hf
  have hex : ∃ P : zeroSet ({f} : Set (MvPolynomial (Fin n) k)),
      eval (P : Fin n → k) (pderiv i f) ≠ 0 := by
    by_contra hnone
    have hall : ∀ x ∈ zeroSet ({f} : Set (MvPolynomial (Fin n) k)),
        eval x (pderiv i f) = 0 := by
      intro x hx
      by_contra hxne
      exact hnone ⟨⟨x, hx⟩, hxne⟩
    have hmem : pderiv i f ∈
        vanishingIdeal k (zeroSet ({f} : Set (MvPolynomial (Fin n) k))) := hall
    rw [vanishingIdeal_zeroSet_singleton_eq_span hf] at hmem
    have hdiv : f ∣ pderiv i f := Ideal.mem_span_singleton.mp hmem
    have hdeg_le : degreeOf i f ≤ degreeOf i (pderiv i f) := by
      obtain ⟨a, ha⟩ := hdiv
      have ha0 : a ≠ 0 := by
        intro ha_zero
        apply hi
        rw [ha, ha_zero, mul_zero]
      rw [ha, degreeOf_mul_eq hf.ne_zero ha0]
      exact Nat.le_add_right _ _
    exact (Nat.not_le_of_lt (degreeOf_pderiv_lt hi)) hdeg_le
  obtain ⟨P, hP⟩ := hex
  exact ⟨P, i, hP⟩

/-- An irreducible affine hypersurface has an affine nonsingular point. -/
theorem exists_affineNonsingularAt_zeroSet_irreducible
    {n : ℕ} {f : MvPolynomial (Fin n) k} (hf : Irreducible f) :
    ∃ P : zeroSet ({f} : Set (MvPolynomial (Fin n) k)),
      IsAffineNonsingularAt
        (zeroSet ({f} : Set (MvPolynomial (Fin n) k))) P := by
  classical
  let Y : Set (Fin n → k) := zeroSet ({f} : Set (MvPolynomial (Fin n) k))
  obtain ⟨P, i, hi⟩ := exists_point_eval_pderiv_ne_zero hf
  obtain ⟨m, hm, hdim⟩ := exists_dim_zeroSet_irreducible hf
  have hvi : Ideal.span (Set.range (fun _ : Fin 1 => f)) = vanishingIdeal k Y := by
    rw [vanishingIdeal_zeroSet_singleton_eq_span hf]
    congr 1
    ext g
    simp
  let A := jacobianMatrix (P : Fin n → k) (fun _ : Fin 1 => f)
  have hentry : A 0 i ≠ 0 := by
    simpa [A, jacobianMatrix] using hi
  have hnlt : ¬ A.rank < 1 := by
    rw [rank_lt_iff_forall_minors_eq_zero]
    push Not
    refine ⟨(fun _ : Fin 1 => 0), (fun _ : Fin 1 => i), ?_, ?_, ?_⟩
    · exact fun _ _ _ => Subsingleton.elim _ _
    · exact fun _ _ _ => Subsingleton.elim _ _
    · simpa using hentry
  have hrank : A.rank = 1 := by
    have hpos : 0 < A.rank := by omega
    have hle : A.rank ≤ 1 := by
      simpa using Matrix.rank_le_card_height A
    omega
  refine ⟨P, (isAffineNonsingularAt_iff_of_dim_eq P hdim).2 ?_⟩
  have hjac : jacobianRank Y P = 1 := by
    rw [← jacobianMatrix_rank_eq_jacobianRank P (fun _ : Fin 1 => f) hvi]
    exact hrank
  rw [hjac]
  simpa [Y, Nat.add_comm] using hm

/-- A variety presented as the zero set of an irreducible polynomial has an
intrinsic nonsingular point. -/
theorem exists_nonsingularAt_of_eq_zeroSet_irreducible
    {n : ℕ} {Y : Set (Fin n → k)} {f : MvPolynomial (Fin n) k}
    (hY : IsAffineVariety Y)
    (hYf : Y = zeroSet ({f} : Set (MvPolynomial (Fin n) k)))
    (hf : Irreducible f) :
    ∃ P : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier,
      Variety.NonsingularAt
        (Variety.ofQuasiAffine hY.isQuasiAffineVariety) P := by
  subst Y
  obtain ⟨P, hP⟩ := exists_affineNonsingularAt_zeroSet_irreducible hf
  let Q : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier :=
    ⟨P.1, P.2⟩
  refine ⟨Q, ?_⟩
  rw [nonsingularAt_affine_iff hY Q]
  exact hP

/-- The hypersurface case of Hartshorne I.5, Theorem 5.3: the singular locus
of an irreducible affine hypersurface is proper and closed; equivalently, its
nonsingular locus is nonempty and open. -/
theorem hypersurface_singularLocus_isProper
    {n : ℕ} {Y : Set (Fin n → k)} {f : MvPolynomial (Fin n) k}
    (hY : IsAffineVariety Y)
    (hYf : Y = zeroSet ({f} : Set (MvPolynomial (Fin n) k)))
    (hf : Irreducible f) :
    let X := Variety.ofQuasiAffine hY.isQuasiAffineVariety
    IsClosed X.SingularLocus ∧
      X.SingularLocus ⊂ Set.univ ∧
      IsOpen {P | X.NonsingularAt P} ∧
      Set.Nonempty {P | X.NonsingularAt P} := by
  classical
  subst Y
  let X := Variety.ofQuasiAffine hY.isQuasiAffineVariety
  have hclosed : IsClosed X.SingularLocus :=
    isClosed_affineSingularLocus hY
  obtain ⟨Q, hQ⟩ := exists_nonsingularAt_of_eq_zeroSet_irreducible hY rfl hf
  have hQX : X.NonsingularAt Q := by
    simpa only [X] using hQ
  have hnotmem : Q ∉ X.SingularLocus := by
    intro hsing
    exact hsing hQX
  have hproper : X.SingularLocus ⊂ Set.univ := by
    rw [Set.ssubset_univ_iff]
    intro heq
    exact hnotmem (heq.symm ▸ Set.mem_univ Q)
  have hopen : IsOpen {P | X.NonsingularAt P} := by
    simpa only [Variety.SingularLocus, Set.compl_ofPred, not_not] using
      hclosed.isOpen_compl
  exact ⟨hclosed, hproper, hopen, ⟨Q, hQX⟩⟩

/-- The same theorem with the affine-variety structure derived directly from
irreducibility of the defining equation. -/
theorem hypersurface_zeroSet_singularLocus_isProper
    {n : ℕ} {f : MvPolynomial (Fin n) k} (hf : Irreducible f) :
    let Y := zeroSet ({f} : Set (MvPolynomial (Fin n) k))
    let hY : IsAffineVariety Y :=
      isAffineVariety_zeroSet_singleton_of_irreducible hf
    let X := Variety.ofQuasiAffine hY.isQuasiAffineVariety
    IsClosed X.SingularLocus ∧
      X.SingularLocus ⊂ Set.univ ∧
      IsOpen {P | X.NonsingularAt P} ∧
      Set.Nonempty {P | X.NonsingularAt P} := by
  exact hypersurface_singularLocus_isProper
    (isAffineVariety_zeroSet_singleton_of_irreducible hf) rfl hf

end Hartshorne
