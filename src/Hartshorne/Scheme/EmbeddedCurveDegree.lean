/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteCurveDivisorPullback
import Hartshorne.Scheme.ProjectiveIntersectionDegree
import Hartshorne.Scheme.ProjectiveIntersectionDegreeFormula
import Hartshorne.Intersection.ProjectivePointDegree
import Hartshorne.Projective.LinearSeparation

/-!
# The degree of an embedded curve and hyperplane sections

Hartshorne, *Algebraic Geometry*, IV, Example 3.3.2 (p. 309), first part of the proof.

Let `k` be algebraically closed and let `ι : X ⟶ ℙⁿ_k = Proj k[x₀, …, xₙ]` be a closed immersion
of a nonsingular curve. A closed point of `ℙⁿ_k` has projective degree one, so for a divisor `E`
on `X` the degree of `E` in the embedding (the weighted sum of the projective degrees of its
points) is the divisor degree `deg E` (`Hartshorne.weilDivisorProjectiveDegree_eq_divisorDegree`).
If the coordinate hyperplane `H = V(xᵢ)` does not contain `X`, then the generalized Bézout theorem
(II, Exercise 6.2(c)) with `deg H = 1` gives `deg ι(X) = deg (H · X)`
(`Hartshorne.projectiveSpectrumPointDegree_eq_divisorDegree_hyperplane`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) k

local notation "S" => MvPolynomial (Fin (n + 1)) k

/-- Points are closed in classical projective space. -/
private theorem isClosed_singleton_projectiveSpace' (P : ProjectiveSpace k (Fin (n + 1))) :
    IsClosed ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) := by
  rw [isClosed_iff_isProjAlgebraicSet]
  refine ⟨homogeneousVanishingSet {P},
    isHomogeneousSet_homogeneousVanishingSet {P},
    Set.Subset.antisymm (subset_projZeroSet_homogeneousVanishingSet {P}) ?_⟩
  intro Q hQ
  by_contra hQP
  have hPQ : P ≠ Q := by
    simpa [Set.mem_singleton_iff, eq_comm] using hQP
  obtain ⟨_, h, _, hh, _, _, hhP, hhQ⟩ :=
    exists_linear_forms_separating_projective_points hPQ
  apply hhQ
  exact hQ h ⟨⟨1, hh⟩, by
    intro R hRP
    rw [Set.mem_singleton_iff.mp hRP]
    exact hhP⟩

/-- **A closed point of `ℙⁿ_k` has degree one** (`k` algebraically closed): the zero set of its
homogeneous prime is a single classical point. -/
theorem projectiveSpectrumPointDegree_of_isClosed [IsAlgClosed k] (x : Proj 𝒜)
    (hx : IsClosed ({x} : Set (Proj 𝒜))) : projectiveSpectrumPointDegree x = 1 := by
  obtain ⟨hYv, hJ⟩ := isProjVariety_projZeroSet_asHomogeneousIdeal x
  obtain ⟨P, hP⟩ := hYv.1.nonempty
  set Q := homogeneousVanishingIdeal ({P} : Set (ProjectiveSpace k (Fin (n + 1))))
  have hQhom : IsHomogeneousIdeal Q := isHomogeneousIdeal_homogeneousVanishingIdeal _
  have hQprime : Q.IsPrime := isPrime_homogeneousVanishingIdeal_singleton P
  have hZQ : projZeroSet (Q : Set S) = {P} := by
    rw [projZeroSet_homogeneousVanishingIdeal_eq_closure,
      (isClosed_singleton_projectiveSpace' P).closure_eq]
  have hrel : ¬(HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Q :=
    (projZeroSet_nonempty_iff_not_irrelevant_le hQhom).mp (by rw [hZQ]; exact ⟨P, rfl⟩)
  let y : Proj 𝒜 := ⟨⟨Q, hQhom⟩, hQprime, hrel⟩
  have hxy : x ⤳ y := by
    rw [projectiveSpace_specializes_iff_le]
    change x.asHomogeneousIdeal.toIdeal ≤ Q
    rw [← hJ]
    exact homogeneousVanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hP)
  have hyx : y = x := by
    have := specializes_iff_mem_closure.mp hxy
    rw [hx.closure_eq] at this
    exact this
  have hxQ : x.asHomogeneousIdeal.toIdeal = Q := by rw [← hyx]
  have h := projectiveSpectrumPointDegree_cast x
  change (projectiveSpectrumPointDegree x : ℚ) =
    projectiveDegree (projZeroSet (x.asHomogeneousIdeal.toIdeal : Set S)) at h
  rw [hxQ, hZQ, (projectivePoint_hilbertPolynomial_and_degree P).2] at h
  exact_mod_cast h

/-- A coordinate hyperplane of `ℙⁿ_k` (`n ≥ 1`) has degree one. -/
theorem projectiveSpectrumPointDegree_hyperplane [IsAlgClosed k] (hn : 0 < n) (i : Fin (n + 1)) :
    projectiveSpectrumPointDegree
      (projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
        (MvPolynomial.X_prime (R := k) (i := i)).irreducible).1 = 1 := by
  set V := projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
    (MvPolynomial.X_prime (R := k) (i := i)).irreducible
  have h := projectiveSpectrumPointDegree_cast V.1
  have hs : (V.1.asHomogeneousIdeal : Set S) = (Ideal.span {(MvPolynomial.X i : S)} : Set S) := by
    rw [← projectiveHypersurfacePrimeDivisor_asHomogeneousIdeal hn (isHomogeneous_X k i)
      (MvPolynomial.X_prime (R := k) (i := i)).irreducible]
    rfl
  rw [hs, projZeroSet_span, (hypersurface_hilbertPolynomial_and_degree hn one_pos _
    (isHomogeneous_X k i) (MvPolynomial.X_prime (R := k) (i := i)).irreducible).2] at h
  exact_mod_cast h

section Curve

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- **Degrees of divisors on an embedded curve.** For a closed immersion `ι : X ⟶ ℙⁿ_k` of a
nonsingular curve (`k` algebraically closed), the degree of a divisor `E` in the embedding, the
weighted sum of the projective degrees of its points, is its divisor degree: closed points of
`ℙⁿ_k` have degree one. -/
theorem weilDivisorProjectiveDegree_eq_divisorDegree [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (E : X.WeilDivisor) :
    weilDivisorProjectiveDegree ι E = hX.divisorDegree E := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  have hdeg : ∀ P : X.PrimeDivisor, primeDivisorProjectiveDegree ι P = 1 := by
    intro P
    apply projectiveSpectrumPointDegree_of_isClosed
    have hP : IsClosed ({P.1} : Set X) := (hX.isClosed_singleton_iff_coheight_eq_one P.1).mpr P.2
    have := ι.isClosedEmbedding.isClosedMap _ hP
    rwa [Set.image_singleton] at this
  rw [weilDivisorProjectiveDegree_apply, Scheme.IsNonsingularCurve.divisorDegree_apply]
  simp only [hdeg, mul_one]
  rw [Finsupp.sum]
  exact finsum_eq_sum_of_support_subset (fun P : X.PrimeDivisor ↦ E.1 P.1) fun P hP ↦
    Finsupp.mem_support_iff.mpr hP

/-- A nonsingular curve has more than one point. -/
theorem nontrivial_of_isNonsingularCurve (hX : X.IsNonsingularCurve k) : Nontrivial X := by
  obtain ⟨x, hx⟩ := hX.exists_ne_genericPoint
  exact ⟨⟨x, genericPoint X, hx⟩⟩

/-- **The degree of an embedded curve is the degree of a hyperplane section** (Hartshorne IV,
Example 3.3.2, first step). Let `k` be algebraically closed, `ι : X ⟶ ℙⁿ_k` (`n ≥ 1`) a closed
immersion of a nonsingular curve, and `H = V(xᵢ)` a coordinate hyperplane not containing `X`, that
is, `xᵢ` does not vanish at the image of the generic point. Then `deg ι(X) = deg (H · X)`, where
`H · X` is the divisor cut on `X` by `H`. -/
theorem projectiveSpectrumPointDegree_eq_divisorDegree_hyperplane [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (hn : 0 < n)
    (i : Fin (n + 1)) (hi : (MvPolynomial.X i : S) ∉ (ι.base (genericPoint X)).asHomogeneousIdeal) :
    projectiveSpectrumPointDegree (ι.base (genericPoint X)) =
      hX.divisorDegree (projectiveIntersectionDivisor ι hX.satisfiesConditionStar
        (projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
          (MvPolynomial.X_prime (R := k) (i := i)).irreducible)) := by
  set V := projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
    (MvPolynomial.X_prime (R := k) (i := i)).irreducible
  have hXV : ¬Set.range ι ⊆ closure ({V.1} : Set (Proj 𝒜)) := fun h ↦ hi <|
    (mem_closure_projectiveHypersurfacePrimeDivisor_iff hn _ _ _).mp (h ⟨genericPoint X, rfl⟩)
  have h := weilDivisorProjectiveDegree_projectiveIntersectionDivisor ι hX.satisfiesConditionStar
    (nontrivial_of_isNonsingularCurve hX) V hXV
  simp only at h
  rw [projectiveSpectrumPointDegree_hyperplane hn i, one_mul,
    weilDivisorProjectiveDegree_eq_divisorDegree hX] at h
  exact h.symm

end Curve

end Hartshorne
