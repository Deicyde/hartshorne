/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.UnionCoordinateRingExact
import Hartshorne.Intersection.ProjectiveHilbertPolynomial

/-!
# Degree of a union

Hartshorne, *Algebraic Geometry*, Proposition I.7.6(b) (p. 52).

If two projective algebraic sets have the same dimension and their intersection
has smaller dimension, then the degree of their union is the sum of their
degrees.  The proof uses the degreewise exact coordinate-ring sequence to add
Hilbert polynomials and then observes that the final quotient, supported on the
intersection, has smaller polynomial degree.
-/

namespace Hartshorne

open DirectSum Filter MvPolynomial Polynomial Set
open scoped Polynomial

noncomputable section

universe u

private theorem homogeneousVanishingIdeal_union
    {k : Type u} [Field k] {σ : Type*}
    (Y₁ Y₂ : Set (ProjectiveSpace k σ)) :
    homogeneousVanishingIdeal (Y₁ ∪ Y₂) =
      homogeneousVanishingIdeal Y₁ ⊓ homogeneousVanishingIdeal Y₂ := by
  apply le_antisymm
  · exact le_inf
      (homogeneousVanishingIdeal_anti_mono Set.subset_union_left)
      (homogeneousVanishingIdeal_anti_mono Set.subset_union_right)
  · let I : Ideal (MvPolynomial σ k) :=
      homogeneousVanishingIdeal Y₁ ⊓ homogeneousVanishingIdeal Y₂
    have hI : IsHomogeneousIdeal I :=
      (isHomogeneousIdeal_homogeneousVanishingIdeal Y₁).inf
        (isHomogeneousIdeal_homogeneousVanishingIdeal Y₂)
    obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists
      (𝒜 := homogeneousSubmodule σ k) (I := I)).mp hI
    rw [show homogeneousVanishingIdeal Y₁ ⊓ homogeneousVanishingIdeal Y₂ = I from rfl,
      hT, Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hfI : (f : MvPolynomial σ k) ∈ I := by
      rw [hT]
      exact Ideal.subset_span ⟨f, hf, rfl⟩
    apply Ideal.subset_span
    refine ⟨isHomogeneousElem_iff.mp f.2, ?_⟩
    intro P hP
    rcases hP with hP | hP
    · exact eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal hfI.1 hP
    · exact eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal hfI.2 hP

private theorem projZeroSet_sup
    {k : Type u} [Field k] {σ : Type*}
    (I J : Ideal (MvPolynomial σ k)) :
    projZeroSet ((I ⊔ J : Ideal (MvPolynomial σ k)) : Set (MvPolynomial σ k)) =
      projZeroSet (I : Set (MvPolynomial σ k)) ∩
        projZeroSet (J : Set (MvPolynomial σ k)) := by
  calc
    projZeroSet ((I ⊔ J : Ideal (MvPolynomial σ k)) : Set (MvPolynomial σ k)) =
        projZeroSet
          (Ideal.span ((I : Set (MvPolynomial σ k)) ∪
            (J : Set (MvPolynomial σ k))) : Set (MvPolynomial σ k)) := by
      rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]
    _ = projZeroSet
        ((I : Set (MvPolynomial σ k)) ∪ (J : Set (MvPolynomial σ k))) :=
      projZeroSet_span _
    _ = _ := by
      ext P
      simp only [Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩
      · rintro ⟨hI, hJ⟩ f (hf | hf)
        · exact hI f hf
        · exact hJ f hf

private theorem polynomial_eq_of_eventually_eval_eq {P Q : ℚ[X]}
    (h : ∀ᶠ d : ℤ in atTop, P.eval (d : ℚ) = Q.eval (d : ℚ)) : P = Q := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  apply Polynomial.eq_of_infinite_eval_eq
  let T : Set ℚ := (fun n : ℕ => (n : ℚ)) '' Set.Ioi N.natAbs
  have hT : T.Infinite :=
    (Set.Ioi_infinite N.natAbs).image
      (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℚ))).injOn
  refine hT.mono ?_
  rintro x ⟨n, hn, rfl⟩
  apply hN (n : ℤ)
  exact Int.le_natAbs.trans (by exact_mod_cast hn.le)

/-- The ambient polynomial-ring action respects the quotient grading attached
to any homogeneous ideal. -/
private instance quotGradingGradedSMul
    {k : Type u} [Field k] {σ : Type*}
    (I : HomogeneousIdeal (integerHomogeneousSubmodule k σ)) :
    SetLike.GradedSMul (integerHomogeneousSubmodule k σ)
      (quotGrading (integerHomogeneousSubmodule k σ) I) where
  smul_mem {i j a q} ha hq := by
    obtain ⟨b, hb, rfl⟩ := hq
    refine ⟨a * b, SetLike.mul_mem_graded ha hb, ?_⟩
    exact Submodule.Quotient.mk_smul I.toIdeal a b

private theorem hilbertFunction_quotGrading_congr
    {k : Type u} [Field k] {n : ℕ}
    (I J : HomogeneousIdeal
      (integerHomogeneousSubmodule k (Fin (n + 1))))
    (h : I = J) (d : ℤ) :
    hilbertFunction (σ := Fin (n + 1))
        (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I) d =
      hilbertFunction (σ := Fin (n + 1))
        (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) J) d := by
  subst J
  rfl

private noncomputable def submoduleProdLinearEquiv
    {k M N : Type*} [Field k]
    [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    (p : Submodule k M) (q : Submodule k N) :
    p.prod q ≃ₗ[k] p × q where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun z := ⟨(z.1.1, z.2.1), ⟨z.1.2, z.2.2⟩⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_smul' r x := by ext <;> rfl

/-- The Hilbert polynomial of the final quotient in the coordinate-ring exact
sequence for `Y₁ ∪ Y₂`.  Its projective support is `Y₁ ∩ Y₂`, although
the quotient need not be the reduced coordinate ring of that intersection. -/
noncomputable def unionIntersectionHilbertPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (Y₁ Y₂ : Set (ProjectiveSpace k (Fin (n + 1)))) : ℚ[X] :=
  gradedHilbertPolynomial
    (k := k) (n := n)
    (M := MvPolynomial (Fin (n + 1)) k ⧸
      (integerProjVanishingIdeal Y₁ ⊔ integerProjVanishingIdeal Y₂).toIdeal)
    (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1)))
      (integerProjVanishingIdeal Y₁ ⊔ integerProjVanishingIdeal Y₂))

/-- Hilbert-polynomial additivity along the coordinate-ring exact sequence for
a union. -/
theorem projectiveHilbertPolynomial_union_add_intersection
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (Y₁ Y₂ : Set (ProjectiveSpace k (Fin (n + 1)))) :
    projectiveHilbertPolynomial Y₁ + projectiveHilbertPolynomial Y₂ =
      projectiveHilbertPolynomial (Y₁ ∪ Y₂) +
        unionIntersectionHilbertPolynomial Y₁ Y₂ := by
  let I₁ := integerProjVanishingIdeal Y₁
  let I₂ := integerProjVanishingIdeal Y₂
  apply polynomial_eq_of_eventually_eval_eq
  filter_upwards
      [(projectiveHilbertPolynomial_isHilbertPolynomial Y₁).2,
        (projectiveHilbertPolynomial_isHilbertPolynomial Y₂).2,
        (projectiveHilbertPolynomial_isHilbertPolynomial (Y₁ ∪ Y₂)).2,
        (gradedHilbertPolynomial_isHilbertPolynomial
          (k := k) (n := n)
          (M := MvPolynomial (Fin (n + 1)) k ⧸ (I₁ ⊔ I₂).toIdeal)
          (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1)))
            (I₁ ⊔ I₂))).2]
      with d h₁ h₂ hU hI
  have hUnion : integerProjVanishingIdeal (Y₁ ∪ Y₂) = I₁ ⊓ I₂ := by
    ext f
    change f ∈ homogeneousVanishingIdeal (Y₁ ∪ Y₂) ↔
      f ∈ homogeneousVanishingIdeal Y₁ ⊓ homogeneousVanishingIdeal Y₂
    rw [homogeneousVanishingIdeal_union]
  have hI' : Polynomial.eval (d : ℚ)
      (unionIntersectionHilbertPolynomial Y₁ Y₂) =
      (hilbertFunction (σ := Fin (n + 1))
        (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1)))
          (I₁ ⊔ I₂)) d : ℚ) := by
    simpa only [unionIntersectionHilbertPolynomial, I₁, I₂] using hI
  letI := unionCoordinateMiddleGradingDecomposition I₁ I₂
  letI : SetLike.GradedSMul (integerHomogeneousSubmodule k (Fin (n + 1)))
      (unionCoordinateMiddleGrading I₁ I₂) :=
    unionCoordinateMiddleGradingGradedSMul I₁ I₂
  obtain ⟨hinj, hexact, hsurj⟩ := unionCoordinateRing_exact I₁ I₂ d
  have hHF := hilbertFunction_add_of_degreewise_exact
    (k := k) (σ := Fin (n + 1))
    (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) (I₁ ⊓ I₂))
    (unionCoordinateMiddleGrading I₁ I₂)
    (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) (I₁ ⊔ I₂))
    d (unionCoordinateToPieces_degree I₁ I₂ d)
    (unionPiecesToIntersection_degree I₁ I₂ d) hinj hexact hsurj
  letI : Module.Finite k
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₁ d) :=
    finite_gradedPiece (k := k) (σ := Fin (n + 1))
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₁) d
  letI : Module.Finite k
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₂ d) :=
    finite_gradedPiece (k := k) (σ := Fin (n + 1))
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₂) d
  have hMiddle :
      hilbertFunction (σ := Fin (n + 1))
          (unionCoordinateMiddleGrading I₁ I₂) d =
        hilbertFunction (σ := Fin (n + 1))
            (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₁) d +
          hilbertFunction (σ := Fin (n + 1))
            (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₂) d := by
    change Module.finrank k
      ((quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₁ d).prod
        (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₂ d)) = _
    rw [(submoduleProdLinearEquiv
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₁ d)
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₂ d)).finrank_eq,
      Module.finrank_prod]
    rfl
  rw [Polynomial.eval_add, Polynomial.eval_add, h₁, h₂, hU, hI']
  have hUnionHF := hilbertFunction_quotGrading_congr
    (integerProjVanishingIdeal (Y₁ ∪ Y₂)) (I₁ ⊓ I₂) hUnion d
  change
    (hilbertFunction (σ := Fin (n + 1))
          (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₁) d : ℚ) +
        hilbertFunction (σ := Fin (n + 1))
          (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I₂) d =
      (hilbertFunction (σ := Fin (n + 1))
          (integerProjCoordGrading (Y₁ ∪ Y₂)) d : ℚ) +
        hilbertFunction (σ := Fin (n + 1))
          (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) (I₁ ⊔ I₂)) d
  rw [hUnionHF]
  rw [hMiddle] at hHF
  exact_mod_cast hHF

/-- The final quotient in the union sequence has Hilbert-polynomial degree
equal to the dimension of the set-theoretic intersection. -/
theorem unionIntersectionHilbertPolynomial_degree
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {Y₁ Y₂ : Set (ProjectiveSpace k (Fin (n + 1)))}
    (hY₁ : IsProjAlgebraicSet Y₁) (hY₂ : IsProjAlgebraicSet Y₂) :
    hilbertPolynomialDegree (unionIntersectionHilbertPolynomial Y₁ Y₂) =
      projDim (Y₁ ∩ Y₂) := by
  rw [unionIntersectionHilbertPolynomial, gradedHilbertPolynomial_degree,
    Ideal.annihilator_quotient, HomogeneousIdeal.toIdeal_sup,
    projZeroSet_sup, hY₁.projZeroSet_homogeneousVanishingIdeal_eq,
    hY₂.projZeroSet_homogeneousVanishingIdeal_eq]

private theorem natDegree_eq_of_hilbertPolynomialDegree_eq_nat
    {P : ℚ[X]} {r : ℕ}
    (h : hilbertPolynomialDegree P = (r : WithBot ℕ∞)) :
    P.natDegree = r := by
  by_cases hP : P = 0
  · simp [hilbertPolynomialDegree, hP] at h
  · simpa [hilbertPolynomialDegree, hP] using h

private theorem projDim_empty
    {k : Type u} [Field k] {σ : Type*} :
    projDim (∅ : Set (ProjectiveSpace k σ)) = ⊥ := by
  unfold projDim topologicalKrullDim
  letI : IsEmpty
      (TopologicalSpace.IrreducibleCloseds
        (↥(∅ : Set (ProjectiveSpace k σ)))) :=
    ⟨fun Z => Z.2.1.nonempty.elim fun x => x.2⟩
  exact Order.krullDim_eq_bot

private theorem nonempty_of_projDim_eq_nat
    {k : Type u} [Field k] {σ : Type*}
    {Y : Set (ProjectiveSpace k σ)} {r : ℕ}
    (h : projDim Y = (r : WithBot ℕ∞)) : Y.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hY
  subst Y
  rw [projDim_empty] at h
  simp at h

/-- **Proposition I.7.6(b).** Degree is additive across a union of two
equidimensional projective algebraic sets when their intersection has smaller
dimension. -/
theorem projectiveDegree_union
    {k : Type u} [Field k] [IsAlgClosed k] {n r : ℕ}
    {Y₁ Y₂ : Set (ProjectiveSpace k (Fin (n + 1)))}
    (hY₁ : IsProjAlgebraicSet Y₁) (hY₂ : IsProjAlgebraicSet Y₂)
    (hY₁dim : projDim Y₁ = (r : WithBot ℕ∞))
    (hY₂dim : projDim Y₂ = (r : WithBot ℕ∞))
    (hInterDim : projDim (Y₁ ∩ Y₂) < (r : WithBot ℕ∞)) :
    projectiveDegree (Y₁ ∪ Y₂) =
      projectiveDegree Y₁ + projectiveDegree Y₂ := by
  let P₁ := projectiveHilbertPolynomial Y₁
  let P₂ := projectiveHilbertPolynomial Y₂
  let PU := projectiveHilbertPolynomial (Y₁ ∪ Y₂)
  let PI := unionIntersectionHilbertPolynomial Y₁ Y₂
  have hP₁deg : P₁.natDegree = r :=
    natDegree_eq_of_hilbertPolynomialDegree_eq_nat <| by
      rw [projectiveHilbertPolynomial_degree hY₁]
      exact hY₁dim
  have hP₂deg : P₂.natDegree = r :=
    natDegree_eq_of_hilbertPolynomialDegree_eq_nat <| by
      rw [projectiveHilbertPolynomial_degree hY₂]
      exact hY₂dim
  have hPIdeg : hilbertPolynomialDegree PI < (r : WithBot ℕ∞) := by
    rw [show hilbertPolynomialDegree PI = projDim (Y₁ ∩ Y₂) by
      exact unionIntersectionHilbertPolynomial_degree hY₁ hY₂]
    exact hInterDim
  have hPIcoeff : PI.coeff r = 0 := by
    by_cases hPI : PI = 0
    · simp [hPI]
    · have hPInat : PI.natDegree < r := by
        unfold hilbertPolynomialDegree at hPIdeg
        simp only [if_neg hPI] at hPIdeg
        exact_mod_cast hPIdeg
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hPInat
  have hY₁ne : Y₁.Nonempty := nonempty_of_projDim_eq_nat hY₁dim
  have hY₂ne : Y₂.Nonempty := nonempty_of_projDim_eq_nat hY₂dim
  have hP₁lc : 0 < P₁.leadingCoeff := by
    have hsupport :
        (projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
            (homogeneousCoordinateRing Y₁) :
              Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
      rw [projZeroSet_annihilator_homogeneousCoordinateRing hY₁]
      exact hY₁ne
    simpa [P₁, projectiveHilbertPolynomial] using
      (gradedHilbertPolynomial_leadingCoeff_pos
        (k := k) (n := n) (M := homogeneousCoordinateRing Y₁)
        (integerProjCoordGrading Y₁) hsupport)
  have hP₂lc : 0 < P₂.leadingCoeff := by
    have hsupport :
        (projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
            (homogeneousCoordinateRing Y₂) :
              Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
      rw [projZeroSet_annihilator_homogeneousCoordinateRing hY₂]
      exact hY₂ne
    simpa [P₂, projectiveHilbertPolynomial] using
      (gradedHilbertPolynomial_leadingCoeff_pos
        (k := k) (n := n) (M := homogeneousCoordinateRing Y₂)
        (integerProjCoordGrading Y₂) hsupport)
  have hpoly : P₁ + P₂ = PU + PI := by
    simpa [P₁, P₂, PU, PI] using
      projectiveHilbertPolynomial_union_add_intersection Y₁ Y₂
  have hcoeff := congrArg (fun P : ℚ[X] => P.coeff r) hpoly
  simp only [Polynomial.coeff_add, hPIcoeff, add_zero] at hcoeff
  have hPUcoeff : PU.coeff r ≠ 0 := by
    rw [← hcoeff]
    have h₁ : 0 < P₁.coeff r := by
      simpa [Polynomial.leadingCoeff, hP₁deg] using hP₁lc
    have h₂ : 0 < P₂.coeff r := by
      simpa [Polynomial.leadingCoeff, hP₂deg] using hP₂lc
    exact ne_of_gt (add_pos h₁ h₂)
  have hPUeq : PU = P₁ + P₂ - PI := eq_sub_of_add_eq hpoly.symm
  have hPIle : PI.natDegree ≤ r := by
    by_cases hPI : PI = 0
    · simp [hPI]
    · have hPInat : PI.natDegree < r := by
        unfold hilbertPolynomialDegree at hPIdeg
        simp only [if_neg hPI] at hPIdeg
        exact_mod_cast hPIdeg
      exact hPInat.le
  have hPUle : PU.natDegree ≤ r := by
    rw [hPUeq]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ hPIle)
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le hP₁deg.le hP₂deg.le)
  have hPUdeg : PU.natDegree = r :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hPUle hPUcoeff
  have hleading : PU.leadingCoeff = P₁.leadingCoeff + P₂.leadingCoeff := by
    simpa [Polynomial.leadingCoeff, hPUdeg, hP₁deg, hP₂deg] using hcoeff.symm
  unfold projectiveDegree
  change PU.natDegree.factorial * PU.leadingCoeff =
    P₁.natDegree.factorial * P₁.leadingCoeff +
      P₂.natDegree.factorial * P₂.leadingCoeff
  rw [hPUdeg, hP₁deg, hP₂deg, hleading]
  ring

end

end Hartshorne
