/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ProjectiveHilbertPolynomial
import Hartshorne.Projective.PointIdeal

namespace Hartshorne

open MvPolynomial Polynomial Set
open scoped Polynomial

noncomputable section

universe u

private noncomputable def pointPieceQuotientMap
    {k : Type u} [Field k] {n d : ℕ}
    (P : ProjectiveSpace k (Fin (n + 1))) :
    homogeneousSubmodule (Fin (n + 1)) k d →ₗ[k]
      projCoordGrading ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) d where
  toFun f := ⟨Ideal.Quotient.mk _ f, ⟨f, f.2, rfl⟩⟩
  map_add' f g := by ext; simp
  map_smul' c f := by
    ext
    change (Ideal.Quotient.mkₐ k _).toLinearMap
        (c • (f : MvPolynomial (Fin (n + 1)) k)) =
      c • (Ideal.Quotient.mkₐ k _).toLinearMap
        (f : MvPolynomial (Fin (n + 1)) k)
    exact (Ideal.Quotient.mkₐ k _).toLinearMap.map_smul c
      (f : MvPolynomial (Fin (n + 1)) k)

private noncomputable def pointPieceEval
    {k : Type u} [Field k] {n : ℕ}
    (P : ProjectiveSpace k (Fin (n + 1))) (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) k d →ₗ[k] k :=
  (MvPolynomial.aeval P.rep).toLinearMap.domRestrict
    (homogeneousSubmodule (Fin (n + 1)) k d)

private theorem pointPieceEval_surjective
    {k : Type u} [Field k] {n : ℕ}
    (P : ProjectiveSpace k (Fin (n + 1))) (d : ℕ) :
    Function.Surjective (pointPieceEval P d) := by
  obtain ⟨i, hi⟩ := exists_mem_standardChart P
  have hi' : P.rep i ≠ 0 := rep_ne_zero_of_mem_standardChart hi
  intro c
  let x : homogeneousSubmodule (Fin (n + 1)) k d :=
    ⟨X i ^ d, (mem_homogeneousSubmodule d (X i ^ d)).2 (by
      simpa using (isHomogeneous_X k i).pow d)⟩
  refine ⟨(c * (P.rep i ^ d)⁻¹) • x, ?_⟩
  simp [pointPieceEval, x, hi']

private theorem pointPiece_ker_eq
    {k : Type u} [Field k] {n d : ℕ}
    (P : ProjectiveSpace k (Fin (n + 1))) :
    LinearMap.ker (pointPieceQuotientMap P (d := d)) =
      LinearMap.ker (pointPieceEval P d) := by
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  simp only [pointPieceQuotientMap, pointPieceEval, LinearMap.domRestrict_apply,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_def]
  have hf : (f : MvPolynomial (Fin (n + 1)) k).IsHomogeneous d :=
    (mem_homogeneousSubmodule d (f : MvPolynomial (Fin (n + 1)) k)).1 f.2
  constructor
  · intro h
    have hq := congrArg Subtype.val h
    change (Ideal.Quotient.mk _ f : homogeneousCoordinateRing ({P} : Set _)) = 0 at hq
    rw [Ideal.Quotient.eq_zero_iff_mem] at hq
    have hv := (mem_homogeneousVanishingIdeal_singleton_iff hf P).1 hq
    simpa [HomogeneousVanish] using hv
  · intro h
    apply Subtype.ext
    change (Ideal.Quotient.mk _ f : homogeneousCoordinateRing ({P} : Set _)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply (mem_homogeneousVanishingIdeal_singleton_iff hf P).2
    simpa [HomogeneousVanish] using h

private theorem pointPieceQuotientMap_surjective
    {k : Type u} [Field k] {n d : ℕ}
    (P : ProjectiveSpace k (Fin (n + 1))) :
    Function.Surjective (pointPieceQuotientMap P (d := d)) := by
  rintro ⟨q, hq⟩
  obtain ⟨f, hf, hfq⟩ := hq
  refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
  exact hfq

private theorem finrank_projCoordGrading_singleton
    {k : Type u} [Field k] {n : ℕ}
    (P : ProjectiveSpace k (Fin (n + 1))) (d : ℕ) :
    Module.finrank k
      (projCoordGrading ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) d) = 1 := by
  let _ : FiniteDimensional k (homogeneousSubmodule (Fin (n + 1)) k d) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin (n + 1)) k d)
  let q := pointPieceQuotientMap P (d := d)
  let e := pointPieceEval P d
  have hq := LinearMap.finrank_range_add_finrank_ker q
  have he := LinearMap.finrank_range_add_finrank_ker e
  rw [LinearMap.range_eq_top.2 (pointPieceQuotientMap_surjective P),
    pointPiece_ker_eq P] at hq
  rw [LinearMap.range_eq_top.2 (pointPieceEval_surjective P d)] at he
  have h := Nat.add_right_cancel (hq.trans he.symm)
  simpa using h

private theorem hilbertFunction_projectivePoint
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (P : ProjectiveSpace k (Fin (n + 1))) (d : ℕ) :
    hilbertFunction (k := k) (σ := Fin (n + 1))
        (integerProjCoordGrading ({P} : Set (ProjectiveSpace k (Fin (n + 1)))))
        (d : ℤ) = 1 := by
  rw [hilbertFunction, integerProjCoordGrading_ofNat]
  exact finrank_projCoordGrading_singleton P d

private theorem one_isHilbertPolynomial_projectivePoint
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (P : ProjectiveSpace k (Fin (n + 1))) :
    IsHilbertPolynomial (σ := Fin (n + 1))
      (integerProjCoordGrading ({P} : Set (ProjectiveSpace k (Fin (n + 1))))) 1 := by
  constructor
  · rw [IsNumericalPolynomial]
    exact Filter.Eventually.of_forall fun _ => ⟨1, by simp⟩
  · rw [Filter.eventually_atTop]
    refine ⟨0, fun d hd => ?_⟩
    obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [hilbertFunction_projectivePoint]
    simp

/-- A projective point has constant Hilbert polynomial one and degree one,
as used in Hartshorne I.7, Corollary 7.8. -/
theorem projectivePoint_hilbertPolynomial_and_degree
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (P : ProjectiveSpace k (Fin (n + 1))) :
    projectiveHilbertPolynomial ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) = 1 ∧
      projectiveDegree ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) = 1 := by
  have hpolynomial :
      projectiveHilbertPolynomial ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) = 1 :=
    isHilbertPolynomial_unique
      (integerProjCoordGrading ({P} : Set (ProjectiveSpace k (Fin (n + 1)))))
      (projectiveHilbertPolynomial_isHilbertPolynomial ({P} : Set _))
      (one_isHilbertPolynomial_projectivePoint P)
  refine ⟨hpolynomial, ?_⟩
  simp [projectiveDegree, hpolynomial]

end

end Hartshorne
