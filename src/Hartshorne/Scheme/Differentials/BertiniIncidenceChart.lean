/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.BertiniIncidenceAmbient
import Hartshorne.Scheme.MorphismFromGeneratedLineBundle
import Hartshorne.Scheme.DimensionCodimension

/-!
# Charts of the Bertini incidence correspondence

Let `X` be a `k`-scheme, `V ⊆ X` an open subset and `μ = (μ_{ℓ j})` an `(r + 1) × (n + 1)`
matrix of functions on `V`. On the chart

`incidenceChart q V β = V ×_k D₊(a_β) ⊆ X ×_k (ℙⁿ_k)^∨`

we consider the functions `τ_ℓ = ∑ⱼ μ_{ℓ j} · a_j / a_β` (`incidenceChartEquation`) and their
common zero locus `chartIncidence q μ β`.

* `mem_chartIncidence_iff`: a point `z` of the chart whose second projection represents the
  vector `a` lies in `chartIncidence q μ β` exactly when every function `∑ⱼ a_j μ_{ℓ j}`
  vanishes at the first projection of `z`.
* `chartIncidence_isIrreducible_and_topologicalKrullDim`: if `X` is integral of finite type
  over `k` of dimension `r < n`, `V` is a nonempty affine open, the columns `J ℓ'` of `μ` form
  an invertible matrix and `β ∉ J`, then `chartIncidence q μ β` is irreducible of dimension
  `n - 1`.

For the second statement, the chart is identified with `Spec Γ(X, V)[y_j : j ≠ β]` (the
coordinates `y_j = a_j / a_β`), under which `τ_ℓ` becomes the affine linear polynomial
`∑ⱼ μ_{ℓ j} y_j` (with `y_β = 1`). Solving the linear system for the variables `y_{J ℓ'}` shows
that the quotient by these polynomials is a polynomial ring over `Γ(X, V)` in the `n - r - 1`
remaining variables, and the common zero locus is homeomorphic to its spectrum.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BertiniIncidence

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
  {V : X.Opens} {r : ℕ} (μ : Fin (r + 1) → Fin (n + 1) → Γ(X, V)) (β : Fin (n + 1))

local notation "𝒮" => homogeneousSubmodule (Fin (n + 1)) k

section Definitions

variable (V) in
/-- The chart `V ×_k D₊(a_β)` of the incidence ambient space `X ×_k (ℙⁿ_k)^∨`. -/
def incidenceChart : (incidenceAmbient q n).Opens :=
  pullback.fst q (dualProjectiveSpaceStructure k n) ⁻¹ᵁ V ⊓
    pullback.snd q (dualProjectiveSpaceStructure k n) ⁻¹ᵁ Proj.basicOpen 𝒮 (MvPolynomial.X β)

variable (V) in
/-- The chart `V ×_k D₊(a_β)` lies over `V`. -/
theorem incidenceChart_le_fst :
    incidenceChart q V β ≤ pullback.fst q (dualProjectiveSpaceStructure k n) ⁻¹ᵁ V :=
  inf_le_left

variable (V) in
/-- The chart `V ×_k D₊(a_β)` lies over `D₊(a_β)`. -/
theorem incidenceChart_le_snd :
    incidenceChart q V β ≤
      pullback.snd q (dualProjectiveSpaceStructure k n) ⁻¹ᵁ Proj.basicOpen 𝒮 (MvPolynomial.X β) :=
  inf_le_right

/-- The function `τ_ℓ = ∑ⱼ μ_{ℓ j} · a_j / a_β` on the chart `V ×_k D₊(a_β)`. -/
def incidenceChartEquation (ℓ : Fin (r + 1)) :
    Γ(incidenceAmbient q n, incidenceChart q V β) :=
  ∑ j, (pullback.fst q (dualProjectiveSpaceStructure k n)).appLE V _
      (incidenceChart_le_fst q V β) (μ ℓ j) *
    (pullback.snd q (dualProjectiveSpaceStructure k n)).appLE _ _
      (incidenceChart_le_snd q V β) (dualChartRatio k n β j)

/-- The common zero locus of the functions `τ_ℓ` inside the chart `V ×_k D₊(a_β)`. -/
def chartIncidence : Set (incidenceAmbient q n) :=
  (incidenceChart q V β : Set (incidenceAmbient q n)) \
    ⋃ ℓ, ((incidenceAmbient q n).basicOpen (incidenceChartEquation q μ β ℓ) :
      Set (incidenceAmbient q n))

end Definitions

section Pointwise

/-- The germ of `f^♯ s` at `y` is the image of the germ of `s` under the stalk map. -/
private theorem bertiniChart_germ_appLE {Y Z : Scheme.{u}} (f : Y ⟶ Z) (U : Z.Opens)
    (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (y : Y) (hy : y ∈ W) (s : Γ(Z, U)) :
    Y.presheaf.germ W y hy (f.appLE U W e s) = f.stalkMap y (Z.presheaf.germ U (f y) (e hy) s) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  exact (Scheme.Hom.germ_stalkMap_apply f U y (e hy) s).symm

/-- **Points of the chart incidence locus.** Let `z` be a point of the chart `V ×_k D₊(a_β)`
whose image in `(ℙⁿ_k)^∨` represents the nonzero vector `a`. Then `z` is a common zero of the
functions `τ_ℓ` exactly when, for every `ℓ`, the function `∑ⱼ a_j μ_{ℓ j}` on `V` vanishes at
the image `x` of `z` in `X`, i.e. its germ lies in the maximal ideal of `𝒪_{X,x}`. -/
theorem mem_chartIncidence_iff {z : incidenceAmbient q n} (hz : z ∈ incidenceChart q V β)
    {a : Fin (n + 1) → k} (ha : a ≠ 0)
    (hza : Represents a (pullback.snd q (dualProjectiveSpaceStructure k n) z)) :
    z ∈ chartIncidence q μ β ↔ ∀ ℓ,
      X.presheaf.germ V (pullback.fst q (dualProjectiveSpaceStructure k n) z)
          (incidenceChart_le_fst q V β hz)
          (∑ j, X.presheaf.map (homOfLE le_top).op (kConst q (a j)) * μ ℓ j) ∈
        IsLocalRing.maximalIdeal
          (X.presheaf.stalk (pullback.fst q (dualProjectiveSpaceStructure k n) z)) := by
  classical
  set g := dualProjectiveSpaceStructure k n
  set fst := pullback.fst q g
  set snd := pullback.snd q g
  have hz1 : fst z ∈ V := incidenceChart_le_fst q V β hz
  have hz2 : snd z ∈ Proj.basicOpen 𝒮 (MvPolynomial.X β) := incidenceChart_le_snd q V β hz
  have haβ : a β ≠ 0 := (represents_mem_basicOpen_iff hza ha β).1 hz2
  let ρ := IsLocalRing.residue ((incidenceAmbient q n).presheaf.stalk z)
  let Φ : Γ(X, V) →+* IsLocalRing.ResidueField ((incidenceAmbient q n).presheaf.stalk z) :=
    ρ.comp ((fst.stalkMap z).hom.comp (X.presheaf.germ V (fst z) hz1).hom)
  let ψ : k →+* IsLocalRing.ResidueField ((incidenceAmbient q n).presheaf.stalk z) :=
    ρ.comp (((incidenceAmbient q n).presheaf.germ ⊤ z trivial).hom.comp (kConst (fst ≫ q)))
  -- constants on `X` restricted to `V`
  have hB : ∀ c : k, Φ (X.presheaf.map (homOfLE le_top).op (kConst q c)) = ψ c := by
    intro c
    simp only [Φ, ψ, RingHom.comp_apply]
    congr 1
    change fst.stalkMap z (X.presheaf.germ V (fst z) hz1
      (X.presheaf.map (homOfLE le_top).op (kConst q c))) = _
    rw [TopCat.Presheaf.germ_res_apply, Scheme.Hom.germ_stalkMap_apply, ← appTop_kConst]
    rfl
  -- constants on the dual projective space
  have hA : ∀ c : k, ρ (snd.stalkMap z
      ((projectiveSpaceScheme k n).presheaf.germ ⊤ (snd z) trivial (dualConst k n c))) =
        ψ c := by
    intro c
    simp only [ψ, RingHom.comp_apply]
    congr 1
    refine (Scheme.Hom.germ_stalkMap_apply snd ⊤ z trivial (dualConst k n c)).trans ?_
    change (incidenceAmbient q n).presheaf.germ ⊤ z trivial (snd.appTop (kConst g c)) = _
    rw [appTop_kConst, ← pullback.condition]
  -- the chart ratios
  have hR : ∀ j, ρ (snd.stalkMap z ((projectiveSpaceScheme k n).presheaf.germ _ (snd z) hz2
      (dualChartRatio k n β j))) = ψ (a j / a β) := by
    intro j
    rw [← hA, ← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff (snd.stalkMap z).hom,
      ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact germ_dualChartRatio_sub_dualConst_mem_maximalIdeal hza haβ hz2 j
  have hτ : ∀ ℓ, ρ ((incidenceAmbient q n).presheaf.germ _ z hz (incidenceChartEquation q μ β ℓ)) =
      (ψ (a β))⁻¹ * Φ (∑ j, X.presheaf.map (homOfLE le_top).op (kConst q (a j)) * μ ℓ j) := by
    intro ℓ
    simp only [incidenceChartEquation, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := bertiniChart_germ_appLE snd (Proj.basicOpen 𝒮 (MvPolynomial.X β))
      (incidenceChart q V β) (incidenceChart_le_snd q V β) z hz (dualChartRatio k n β j)
    rw [hB, bertiniChart_germ_appLE]
    erw [e1]
    rw [hR, map_div₀]
    simp only [Φ, RingHom.comp_apply]
    ring
  have hψ : ψ (a β) ≠ 0 := (map_ne_zero ψ).2 haβ
  have hρ : ∀ x, ρ x = 0 ↔ x ∈ IsLocalRing.maximalIdeal _ := IsLocalRing.residue_eq_zero_iff
  simp only [chartIncidence, Set.mem_sdiff, Set.mem_iUnion, not_exists]
  refine (and_iff_right hz).trans (forall_congr' fun ℓ => ?_)
  rw [SetLike.mem_coe, Scheme.mem_basicOpen _ _ _ hz, ← IsLocalRing.notMem_maximalIdeal, not_not,
    ← hρ, hτ, mul_eq_zero, or_iff_right (inv_ne_zero hψ)]
  simp only [Φ, RingHom.comp_apply]
  rw [hρ, ← not_iff_not, IsLocalRing.notMem_maximalIdeal, IsLocalRing.notMem_maximalIdeal]
  exact isUnit_map_iff (fst.stalkMap z).hom _

end Pointwise


section Algebra

/-- `dim A[x₁, …, xₘ] = dim A + m` for a Noetherian ring `A`. -/
private theorem bertiniChart_ringKrullDim_mvPolynomial_fin (A : Type*) [CommRing A]
    [IsNoetherianRing A] : ∀ m : ℕ, ringKrullDim (MvPolynomial (Fin m) A) = ringKrullDim A + m
  | 0 => by simp
  | m + 1 => by
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.finSuccEquiv A m).toRingEquiv,
      Polynomial.ringKrullDim_of_isNoetherianRing, bertiniChart_ringKrullDim_mvPolynomial_fin A m,
      Nat.cast_succ, add_assoc]

/-- `dim A[x_s : s ∈ S] = dim A + #S` for a Noetherian ring `A` and a finite type `S`. -/
private theorem bertiniChart_ringKrullDim_mvPolynomial (A : Type*) [CommRing A]
    [IsNoetherianRing A] (S : Type*) [Finite S] :
    ringKrullDim (MvPolynomial S A) = ringKrullDim A + Nat.card S := by
  have := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card,
    ringKrullDim_eq_of_ringEquiv (MvPolynomial.renameEquiv A (Fintype.equivFin S)).toRingEquiv,
    bertiniChart_ringKrullDim_mvPolynomial_fin]

/-- `∑ₗ' φ(M ℓ ℓ') ∑ₗ'' φ(N ℓ' ℓ'') Q ℓ'' = Q ℓ` when `M N = 1`. -/
private theorem bertiniChart_sum_mul_sum {A R : Type*} [CommRing A] [CommRing R] {m : ℕ}
    (φ : A →+* R) {M N : Fin m → Fin m → A} (hMN : Matrix.of M * Matrix.of N = 1)
    (Q : Fin m → R) (ℓ : Fin m) : ∑ ℓ', φ (M ℓ ℓ') * ∑ ℓ'', φ (N ℓ' ℓ'') * Q ℓ'' = Q ℓ := by
  have h := congrFun (Matrix.mulVec_mulVec Q ((Matrix.of M).map φ) ((Matrix.of N).map φ)) ℓ
  rw [← Matrix.map_mul, hMN, Matrix.map_one φ φ.map_zero φ.map_one, Matrix.one_mulVec] at h
  simpa [Matrix.mulVec, dotProduct] using h

open scoped Classical

variable {A : Type u} [CommRing A] {n r : ℕ}

/-- Splitting a sum over `Fin (n + 1)` into the indices outside the range of `J` and those in
the range of `J`. -/
private theorem bertiniChart_sum_split {R : Type*} [CommRing R] (J : Fin (r + 1) ↪ Fin (n + 1))
    (c w : Fin (n + 1) → R) (u : Fin (r + 1) → R) (hw : ∀ ℓ, w (J ℓ) = u ℓ) :
    ∑ j, c j * w j =
      ∑ j, c j * (if j ∈ Set.range J then 0 else w j) + ∑ ℓ, c (J ℓ) * u ℓ := by
  have h1 : ∀ j, c j * w j = c j * (if j ∈ Set.range J then 0 else w j) +
      (if j ∈ Set.range J then c j * w j else 0) := by
    intro j
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib, ← Finset.sum_filter]
  congr 1
  have h2 : Finset.univ.filter (· ∈ Set.range J) = Finset.univ.map J := by
    ext j
    simp
  rw [h2, Finset.sum_map]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [hw]

/-- The affine coordinates `y_j` (`j ≠ β`) of the chart `D₊(a_β)`, together with `y_β = 1`. -/
private def bertiniChartCoord (β j : Fin (n + 1)) : MvPolynomial {j // j ≠ β} A :=
  if h : j = β then 1 else MvPolynomial.X ⟨j, h⟩

/-- The affine linear polynomials `∑ⱼ μ_{ℓ j} y_j` on the chart `D₊(a_β)`. -/
private def bertiniChartPoly (μ : Fin (r + 1) → Fin (n + 1) → A) (β : Fin (n + 1))
    (ℓ : Fin (r + 1)) : MvPolynomial {j // j ≠ β} A :=
  ∑ j, C (μ ℓ j) * bertiniChartCoord β j

/-- The indices which are neither `β` nor in the range of `J`. -/
private abbrev BertiniFreeIdx (β : Fin (n + 1)) (J : Fin (r + 1) ↪ Fin (n + 1)) : Type :=
  {j : Fin (n + 1) // j ≠ β ∧ j ∉ Set.range J}

/-- There are `n - r - 1` indices outside `J ∪ {β}`. -/
private theorem bertiniFreeIdx_card (β : Fin (n + 1)) (J : Fin (r + 1) ↪ Fin (n + 1))
    (hβ : β ∉ Set.range J) : Nat.card (BertiniFreeIdx β J) = n - r - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : Finset.univ.filter (fun j : Fin (n + 1) => j ≠ β ∧ j ∉ Set.range J) =
      (insert β (Finset.univ.map J))ᶜ := by
    ext j
    simp
  have hβ' : β ∉ Finset.univ.map J := by simpa using hβ
  rw [h, Finset.card_compl, Finset.card_insert_of_notMem hβ', Finset.card_map]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

variable (μ : Fin (r + 1) → Fin (n + 1) → A) (β : Fin (n + 1)) (J : Fin (r + 1) ↪ Fin (n + 1))

/-- The coordinates of the solved system: `0` on the range of `J`, `1` at `β`. -/
private def bertiniFreeCoord (j : Fin (n + 1)) : MvPolynomial (BertiniFreeIdx β J) A :=
  if h : j ∈ Set.range J then 0 else if h' : j = β then 1 else MvPolynomial.X ⟨j, h', h⟩

/-- The part `∑_{j ∉ J} μ_{ℓ j} y_j` of the `ℓ`-th equation. -/
private def bertiniFreePart (ℓ : Fin (r + 1)) : MvPolynomial (BertiniFreeIdx β J) A :=
  ∑ j, C (μ ℓ j) * bertiniFreeCoord β J j

/-- The entries of the inverse of the matrix `(μ_{ℓ, J ℓ'})`. -/
private def bertiniInv (ℓ' ℓ : Fin (r + 1)) : A :=
  (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ'))⁻¹ ℓ' ℓ

/-- The solution `y_{J ℓ'} = -∑ₗ (M⁻¹)_{ℓ' ℓ} ∑_{j ∉ J} μ_{ℓ j} y_j` of the linear system. -/
private def bertiniSolution (ℓ' : Fin (r + 1)) : MvPolynomial (BertiniFreeIdx β J) A :=
  -∑ ℓ, C (bertiniInv μ J ℓ' ℓ) * bertiniFreePart μ β J ℓ

/-- Substituting the solution of the linear system. -/
private def bertiniSubst : MvPolynomial {j // j ≠ β} A →ₐ[A] MvPolynomial (BertiniFreeIdx β J) A :=
  aeval fun i => if h : i.1 ∈ Set.range J then bertiniSolution μ β J h.choose else
    MvPolynomial.X ⟨i.1, i.2, h⟩

variable {μ β J}

/-- The substitution sends `y_{J ℓ}` to the solution of the linear system. -/
private theorem bertiniSubst_coord (hβ : β ∉ Set.range J) (ℓ : Fin (r + 1)) :
    bertiniSubst μ β J (bertiniChartCoord β (J ℓ)) = bertiniSolution μ β J ℓ := by
  have hne : J ℓ ≠ β := fun h => hβ ⟨ℓ, h⟩
  have hmem : J ℓ ∈ Set.range J := ⟨ℓ, rfl⟩
  rw [bertiniChartCoord, dif_neg hne, bertiniSubst, aeval_X, dif_pos hmem]
  congr 1
  exact J.injective hmem.choose_spec

/-- The substitution kills the affine linear polynomials `∑ⱼ μ_{ℓ j} y_j`. -/
private theorem bertiniSubst_chartPoly (hdet : IsUnit (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det)
    (hβ : β ∉ Set.range J) (ℓ : Fin (r + 1)) :
    bertiniSubst μ β J (bertiniChartPoly μ β ℓ) = 0 := by
  have hC : ∀ a, bertiniSubst μ β J (C a) = C a := fun a => MvPolynomial.algHom_C _ a
  simp only [bertiniChartPoly, map_sum, map_mul, hC]
  rw [bertiniChart_sum_split J _ _ _ (bertiniSubst_coord hβ)]
  have h1 : ∀ j, (if j ∈ Set.range J then 0 else bertiniSubst μ β J (bertiniChartCoord β j)) =
      bertiniFreeCoord β J j := by
    intro j
    by_cases hj : j ∈ Set.range J
    · rw [if_pos hj, bertiniFreeCoord, dif_pos hj]
    · rw [if_neg hj, bertiniFreeCoord, dif_neg hj, bertiniChartCoord]
      by_cases hjβ : j = β
      · rw [dif_pos hjβ, dif_pos hjβ, map_one]
      · rw [dif_neg hjβ, dif_neg hjβ, bertiniSubst, aeval_X, dif_neg hj]
  simp only [h1, bertiniSolution, mul_neg, Finset.sum_neg_distrib]
  have h2 := bertiniChart_sum_mul_sum (C : A →+* MvPolynomial (BertiniFreeIdx β J) A)
    (M := fun ℓ ℓ' => μ ℓ (J ℓ')) (N := bertiniInv μ J) (Matrix.mul_nonsing_inv _ hdet)
    (bertiniFreePart μ β J) ℓ
  change bertiniFreePart μ β J ℓ + _ = 0
  linear_combination -h2

variable (μ β) in
/-- The ideal generated by the affine linear polynomials `∑ⱼ μ_{ℓ j} y_j`. -/
private abbrev bertiniChartIdeal : Ideal (MvPolynomial {j // j ≠ β} A) :=
  Ideal.span (Set.range (bertiniChartPoly μ β))

/-- Substituting the solution of the linear system, on the quotient. -/
private def bertiniQuotSubst (hdet : IsUnit (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det)
    (hβ : β ∉ Set.range J) :
    (MvPolynomial {j // j ≠ β} A ⧸ bertiniChartIdeal μ β) →ₐ[A]
      MvPolynomial (BertiniFreeIdx β J) A :=
  Ideal.Quotient.liftₐ _ (bertiniSubst μ β J) (fun a ha => by
    have hle : bertiniChartIdeal μ β ≤ RingHom.ker (bertiniSubst μ β J) :=
      Ideal.span_le.2 (Set.range_subset_iff.2 fun ℓ =>
        (RingHom.mem_ker).2 (bertiniSubst_chartPoly hdet hβ ℓ))
    exact (RingHom.mem_ker).1 (hle ha))

/-- The substitution on the quotient, evaluated on a class. -/
private theorem bertiniQuotSubst_mk (hdet : IsUnit (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det)
    (hβ : β ∉ Set.range J) (a : MvPolynomial {j // j ≠ β} A) :
    bertiniQuotSubst hdet hβ (Ideal.Quotient.mk _ a) = bertiniSubst μ β J a :=
  rfl

variable (μ β J) in
/-- The inclusion of the free variables into the quotient. -/
private def bertiniQuotIncl :
    MvPolynomial (BertiniFreeIdx β J) A →ₐ[A] MvPolynomial {j // j ≠ β} A ⧸ bertiniChartIdeal μ β :=
  aeval fun s => Ideal.Quotient.mkₐ A _ (MvPolynomial.X ⟨s.1, s.2.1⟩)

/-- The inclusion of the free variables on the solved coordinates. -/
private theorem bertiniQuotIncl_freeCoord (j : Fin (n + 1)) :
    bertiniQuotIncl μ β J (bertiniFreeCoord β J j) =
      Ideal.Quotient.mk _ (if j ∈ Set.range J then 0 else bertiniChartCoord β j) := by
  rw [bertiniFreeCoord]
  by_cases hj : j ∈ Set.range J
  · rw [dif_pos hj, if_pos hj, map_zero, map_zero]
  · rw [dif_neg hj, if_neg hj, bertiniChartCoord]
    by_cases hjβ : j = β
    · rw [dif_pos hjβ, dif_pos hjβ, map_one, map_one]
    · rw [dif_neg hjβ, dif_neg hjβ, bertiniQuotIncl, aeval_X]
      rfl

/-- In the quotient, `y_{J ℓ₀}` equals the solution of the linear system. -/
private theorem bertiniQuotIncl_solution (hdet : IsUnit (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det)
    (ℓ₀ : Fin (r + 1)) :
    bertiniQuotIncl μ β J (bertiniSolution μ β J ℓ₀) =
      Ideal.Quotient.mk _ (bertiniChartCoord β (J ℓ₀)) := by
  set mk := Ideal.Quotient.mk (bertiniChartIdeal μ β)
  have hC : ∀ a, bertiniQuotIncl μ β J (C a) = mk (C a) := fun a => by
    rw [bertiniQuotIncl, aeval_C]
    rfl
  have key : ∀ ℓ, bertiniQuotIncl μ β J (bertiniFreePart μ β J ℓ) =
      -∑ ℓ', mk (C (μ ℓ (J ℓ'))) * mk (bertiniChartCoord β (J ℓ')) := by
    intro ℓ
    have h0 : mk (bertiniChartPoly μ β ℓ) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨ℓ, rfl⟩)
    rw [bertiniChartPoly, bertiniChart_sum_split J _ _ (fun ℓ' => bertiniChartCoord β (J ℓ'))
      (fun _ => rfl)] at h0
    simp only [map_add, map_sum, map_mul] at h0
    simp only [bertiniFreePart, map_sum, map_mul, hC, bertiniQuotIncl_freeCoord]
    linear_combination h0
  simp only [bertiniSolution, map_neg, map_sum, map_mul, hC, key]
  have h := bertiniChart_sum_mul_sum (mk.comp C) (M := bertiniInv μ J)
    (N := fun ℓ ℓ' => μ ℓ (J ℓ')) (Matrix.nonsing_inv_mul _ hdet)
    (fun ℓ' => mk (bertiniChartCoord β (J ℓ'))) ℓ₀
  simp only [RingHom.comp_apply] at h
  rw [← h, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

variable (hdet : IsUnit (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det) (hβ : β ∉ Set.range J)

include hdet hβ in
/-- **Solving the linear system.** If the columns `J` of `μ` form an invertible matrix and
`β ∉ J`, then `A[y_j : j ≠ β] / (∑ⱼ μ_{ℓ j} y_j)_ℓ` (with `y_β = 1`) is a polynomial ring over `A`
in the variables `y_j`, `j ∉ J ∪ {β}`. -/
private def bertiniQuotEquiv :
    (MvPolynomial {j // j ≠ β} A ⧸ bertiniChartIdeal μ β) ≃ₐ[A]
      MvPolynomial (BertiniFreeIdx β J) A :=
  AlgEquiv.ofAlgHom (bertiniQuotSubst hdet hβ) (bertiniQuotIncl μ β J)
    (MvPolynomial.algHom_ext fun s => by
      rw [AlgHom.comp_apply, bertiniQuotIncl, aeval_X, Ideal.Quotient.mkₐ_eq_mk,
        bertiniQuotSubst_mk, bertiniSubst, aeval_X, dif_neg s.2.2, AlgHom.id_apply])
    (Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, bertiniQuotSubst_mk,
        bertiniSubst, aeval_X, AlgHom.comp_apply, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk]
      by_cases hi : i.1 ∈ Set.range J
      · rw [dif_pos hi, bertiniQuotIncl_solution hdet, bertiniChartCoord,
          dif_neg (fun h => hβ ⟨_, h⟩)]
        congr 2
        exact Subtype.ext hi.choose_spec
      · rw [dif_neg hi, bertiniQuotIncl, aeval_X]
        rfl))

end Algebra

section Chart

/-- `(a ⊗ 1) (1 ⊗ b) = a ⊗ b`. -/
private theorem bertiniChart_tmul_one_mul_one_tmul {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (a : A) (b : B) :
    (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) = a ⊗ₜ[R] b := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- A point lies in the basic open of `f^♯ s` exactly when its image lies in the basic open
of `s`. -/
private theorem bertiniChart_mem_basicOpen_appLE {Y Z : Scheme.{u}} (f : Y ⟶ Z) (U : Z.Opens)
    (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (y : Y) (hy : y ∈ W) (s : Γ(Z, U)) :
    y ∈ Y.basicOpen (f.appLE U W e s) ↔ f y ∈ Z.basicOpen s := by
  rw [Scheme.mem_basicOpen Y _ y hy, Scheme.mem_basicOpen Z s (f y) (e hy),
    bertiniChart_germ_appLE]
  exact isUnit_map_iff (f.stalkMap y).hom _

/-- Transport of `f^♯` along an equality of morphisms. -/
private theorem bertiniChart_appLE_eq_of_eq {Y Z : Scheme.{u}} {f f' : Y ⟶ Z} (h : f = f')
    (U : Z.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (s : Γ(Z, U)) :
    f.appLE U W e s = f'.appLE U W (h ▸ e) s := by
  subst h
  rfl

/-- The canonical morphism `Spec Γ(Y, U) ⟶ Y` of an affine open induces the canonical map
`Γ(Y, U) → Γ(Spec Γ(Y, U), ⊤)`. -/
private theorem bertiniChart_fromSpec_appLE {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(Y, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) (s : Γ(Y, U)) :
    hU.fromSpec.appLE U ⊤ e s = (Scheme.ΓSpecIso Γ(Y, U)).inv s := by
  have hid : ∀ h : Opposite.op (⊤ : (Spec Γ(Y, U)).Opens) ⟶ Opposite.op ⊤,
      (Spec Γ(Y, U)).presheaf.map h = 𝟙 _ := fun h => by
    rw [Subsingleton.elim h (𝟙 _), CategoryTheory.Functor.map_id]
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, hU.fromSpec_app_self_apply,
    ← CommRingCat.comp_apply, ← Functor.map_comp, hid, CommRingCat.id_apply]

/-- On global sections, `Spec.map φ` induces `φ`. -/
private theorem bertiniChart_SpecMap_appLE {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (e : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤) (x : R) :
    (Spec.map φ).appLE ⊤ ⊤ e ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (φ x) := by
  have h1 : (Spec.map φ).appLE ⊤ ⊤ e = (Spec.map φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h1]
  have h := congr($(Scheme.ΓSpecIso_inv_naturality φ) x)
  simp only [CommRingCat.comp_apply] at h
  exact h.symm

/-- The constants of `k` pulled back to the chart `D₊(a_β)` are the constants `c / 1`. -/
private theorem bertiniChart_structure_appLE (β : Fin (n + 1)) (c : k) :
    (Proj.toSpecZero 𝒮 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒮 0)))).appLE ⊤
        (Proj.basicOpen 𝒮 (MvPolynomial.X β)) (show _ ≤ _ ⁻¹ᵁ ⊤ from le_top)
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) =
      Proj.awayToSection 𝒮 (MvPolynomial.X β) (chartConst k β c) := by
  have h1 := ι_comp_eq_toSpecΓ_SpecMap_of_Spec
    (Proj.toSpecZero 𝒮 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒮 0))))
    (Proj.basicOpen 𝒮 (MvPolynomial.X β)) (show _ ≤ _ ⁻¹ᵁ ⊤ from le_top)
  have h2 : (Proj.basicOpen 𝒮 (MvPolynomial.X β)).ι ≫ Proj.toSpecZero 𝒮 ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (𝒮 0))) =
      (Proj.basicOpen 𝒮 (MvPolynomial.X β)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (chartConst k β) ≫
          Proj.awayToSection 𝒮 (MvPolynomial.X β)) := by
    rw [← Iso.hom_inv_id_assoc
      (Proj.basicOpenIsoSpec 𝒮 (MvPolynomial.X β) (X_mem_homogeneousSubmodule_one k β)
        Nat.one_pos) (Proj.basicOpen 𝒮 (MvPolynomial.X β)).ι, Proj.basicOpenIsoSpec_inv_ι,
      Category.assoc, Proj.awayι_toSpecZero_assoc, Proj.basicOpenIsoSpec_hom,
      Proj.basicOpenToSpec, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [h1] at h2
  have h3 := congrArg Scheme.Hom.appTop h2
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc, cancel_epi, cancel_mono] at h3
  have h4 := congr($h3 c)
  simp only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom] at h4
  exact h4

/-- **Affine charts of a fibre product over a field.** Let `V ⊆ X` and `D ⊆ Y` be affine opens of
`k`-schemes, and suppose that `Γ(Y, D)` is identified with a polynomial ring `k[y_j : j ≠ β]` in
such a way that the sections `ρ_j` correspond to the coordinates `y_j` (and `ρ_β` to `1`). Then
`V ×_k D` is the image of an open immersion from `Spec R`, with `R ≅ Γ(X, V)[y_j : j ≠ β]`,
such that the basic open of `∑ⱼ μ_{ℓ j} ρ_j` is the basic open of `∑ⱼ μ_{ℓ j} y_j`. -/
private theorem bertiniChart_general {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k))
    (hV : IsAffineOpen V) {D : Y.Opens} (hD : IsAffineOpen D) (ρ : Fin (n + 1) → Γ(Y, D))
    (eB : CommRingCat.of (MvPolynomial {j // j ≠ β} Γ(Spec (CommRingCat.of k), ⊤)) ≅ Γ(Y, D))
    (hC : ∀ c, eB.hom (C c) = g.appLE ⊤ D le_top c)
    (hρ : ∀ j, eB.hom (bertiniChartCoord β j) = ρ j) :
    ∃ (R : CommRingCat.{u}) (G : Spec R ⟶ pullback q g) (τ' : Fin (r + 1) → R)
      (e : R ≃+* MvPolynomial {j // j ≠ β} Γ(X, V)), IsOpenImmersion G ∧
      Set.range G = (pullback.fst q g ⁻¹ᵁ V ⊓ pullback.snd q g ⁻¹ᵁ D : (pullback q g).Opens) ∧
      (∀ ℓ (w : Spec R), G w ∈ (pullback q g).basicOpen
          (∑ j, (pullback.fst q g).appLE V (pullback.fst q g ⁻¹ᵁ V ⊓ pullback.snd q g ⁻¹ᵁ D)
            inf_le_left (μ ℓ j) * (pullback.snd q g).appLE D _ inf_le_right (ρ j)) ↔
        τ' ℓ ∉ PrimeSpectrum.asIdeal w) ∧
      ∀ ℓ, e (τ' ℓ) = bertiniChartPoly μ β ℓ := by
  classical
  set fst := pullback.fst q g
  set snd := pullback.snd q g
  have hW : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hVW : V ≤ q ⁻¹ᵁ ⊤ := le_top
  have hDW : D ≤ g ⁻¹ᵁ ⊤ := le_top
  let K := Γ(Spec (CommRingCat.of k), ⊤)
  let A := Γ(X, V)
  let B := Γ(Y, D)
  let _ : Algebra K A := (q.appLE ⊤ V hVW).hom.toAlgebra
  let _ : Algebra K B := (g.appLE ⊤ D hDW).hom.toAlgebra
  let m := pullback.map (Spec.map (q.appLE ⊤ V hVW)) (Spec.map (g.appLE ⊤ D hDW)) q g
    hV.fromSpec hD.fromSpec hW.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec q hW hV hVW)
    (IsAffineOpen.SpecMap_appLE_fromSpec g hW hD hDW)
  let G : Spec (.of (A ⊗[K] B)) ⟶ pullback q g := (pullbackSpecIso K A B).inv ≫ m
  have hGfst : G ≫ fst =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ hV.fromSpec := by
    simp only [G, m, Category.assoc, fst, pullback.lift_fst]
    exact pullbackSpecIso_inv_fst_assoc _ _ _ _
  have hGsnd : G ≫ snd =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[K] A ⊗[K] B).toRingHom) ≫ hD.fromSpec := by
    simp only [G, m, Category.assoc, snd, pullback.lift_snd]
    exact pullbackSpecIso_inv_snd_assoc _ _ _ _
  have hG : IsOpenImmersion G := by dsimp only [G, m]; infer_instance
  have hrange : Set.range G = (fst ⁻¹ᵁ V ⊓ snd ⁻¹ᵁ D : (pullback q g).Opens) := by
    have h1 : ((fst ⁻¹ᵁ V ⊓ snd ⁻¹ᵁ D : (pullback q g).Opens) : Set ↥(pullback q g)) =
        fst ⁻¹' Set.range hV.fromSpec ∩ snd ⁻¹' Set.range hD.fromSpec := by
      rw [hV.range_fromSpec, hD.range_fromSpec]
      rfl
    have hm : Set.range m = fst ⁻¹' Set.range hV.fromSpec ∩ snd ⁻¹' Set.range hD.fromSpec :=
      Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _
    rw [h1, ← hm]
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(pullbackSpecIso K A B).inv w, by rw [← Scheme.Hom.comp_apply]⟩
    · rintro ⟨w, rfl⟩
      refine ⟨(pullbackSpecIso K A B).hom w, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hle : (⊤ : (Spec (.of (A ⊗[K] B))).Opens) ≤ G ⁻¹ᵁ (fst ⁻¹ᵁ V ⊓ snd ⁻¹ᵁ D) := by
    intro w _
    change G w ∈ ((fst ⁻¹ᵁ V ⊓ snd ⁻¹ᵁ D : (pullback q g).Opens) : Set ↥(pullback q g))
    rw [← hrange]
    exact ⟨w, rfl⟩
  let τ' : Fin (r + 1) → A ⊗[K] B := fun ℓ => ∑ j, μ ℓ j ⊗ₜ[K] ρ j
  have hfst : ∀ s : A, G.appLE _ ⊤ hle (fst.appLE V _ inf_le_left s) =
      (Scheme.ΓSpecIso (.of (A ⊗[K] B))).inv (s ⊗ₜ[K] 1) := by
    intro s
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      bertiniChart_appLE_eq_of_eq hGfst,
      ← Scheme.Hom.appLE_comp_appLE _ _ V ⊤ ⊤ hV.fromSpec_preimage_self.ge
        (Scheme.Hom.preimage_top _).ge,
      CommRingCat.comp_apply, bertiniChart_fromSpec_appLE, bertiniChart_SpecMap_appLE]
    rfl
  have hsnd : ∀ t : B, G.appLE _ ⊤ hle (snd.appLE D _ inf_le_right t) =
      (Scheme.ΓSpecIso (.of (A ⊗[K] B))).inv (1 ⊗ₜ[K] t) := by
    intro t
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      bertiniChart_appLE_eq_of_eq hGsnd,
      ← Scheme.Hom.appLE_comp_appLE _ _ D ⊤ ⊤ hD.fromSpec_preimage_self.ge
        (Scheme.Hom.preimage_top _).ge,
      CommRingCat.comp_apply, bertiniChart_fromSpec_appLE]
    exact (bertiniChart_SpecMap_appLE (R := B) _ _ t).trans rfl
  have hsec : ∀ ℓ, G.appLE _ ⊤ hle (∑ j, fst.appLE V (fst ⁻¹ᵁ V ⊓ snd ⁻¹ᵁ D) inf_le_left (μ ℓ j) *
      snd.appLE D _ inf_le_right (ρ j)) = (Scheme.ΓSpecIso (.of (A ⊗[K] B))).inv (τ' ℓ) := by
    intro ℓ
    simp only [map_sum, map_mul, τ']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfst, hsnd, ← map_mul, bertiniChart_tmul_one_mul_one_tmul (R := K)]
  -- the ring isomorphism `A ⊗_K B ≃ A[y]`
  let eB' : MvPolynomial {j // j ≠ β} K ≃ₐ[K] B :=
    AlgEquiv.ofRingEquiv (f := eB.commRingCatIsoToRingEquiv) hC
  let e : A ⊗[K] B ≃+* MvPolynomial {j // j ≠ β} A :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[K] A) eB'.symm).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv K A).toRingEquiv
  have hcoord : ∀ j, MvPolynomial.map (algebraMap K A) (bertiniChartCoord β j) =
      (bertiniChartCoord β j : MvPolynomial {j // j ≠ β} A) := by
    intro j
    unfold bertiniChartCoord
    split_ifs <;> simp
  have he : ∀ ℓ, e (τ' ℓ) = bertiniChartPoly μ β ℓ := by
    intro ℓ
    simp only [τ', map_sum, bertiniChartPoly]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : eB'.symm (ρ j) = bertiniChartCoord β j := by
      rw [AlgEquiv.symm_apply_eq]
      exact (hρ j).symm
    simp [e, h1, hcoord, MvPolynomial.smul_eq_C_mul]
  refine ⟨.of (A ⊗[K] B), G, τ', e, hG, hrange, fun ℓ w => ?_, he⟩
  rw [← bertiniChart_mem_basicOpen_appLE G _ ⊤ hle w trivial, hsec, basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- **The chart as an affine scheme.** The chart `V ×_k D₊(a_β)` is the image of an open
immersion from `Spec R`, where `R ≅ Γ(X, V)[y_j : j ≠ β]`, such that the functions `τ_ℓ`
correspond to the polynomials `∑ⱼ μ_{ℓ j} y_j` (with `y_β = 1`). -/
private theorem bertiniChart_exists_chart (hV : IsAffineOpen V) :
    ∃ (R : CommRingCat.{u}) (G : Spec R ⟶ incidenceAmbient q n) (τ' : Fin (r + 1) → R)
      (e : R ≃+* MvPolynomial {j // j ≠ β} Γ(X, V)), IsOpenImmersion G ∧
      Set.range G = (incidenceChart q V β : Set (incidenceAmbient q n)) ∧
      (∀ ℓ (w : Spec R), G w ∈ (incidenceAmbient q n).basicOpen (incidenceChartEquation q μ β ℓ) ↔
        τ' ℓ ∉ PrimeSpectrum.asIdeal w) ∧
      ∀ ℓ, e (τ' ℓ) = bertiniChartPoly μ β ℓ := by
  classical
  have hD : IsAffineOpen (Proj.basicOpen 𝒮 (MvPolynomial.X β)) :=
    Proj.isAffineOpen_basicOpen 𝒮 (MvPolynomial.X β) (X_mem_homogeneousSubmodule_one k β)
      Nat.one_pos
  let e₁ : CommRingCat.of (MvPolynomial {j // j ≠ β} Γ(Spec (CommRingCat.of k), ⊤)) ≅
      CommRingCat.of (MvPolynomial {j // j ≠ β} k) :=
    (MvPolynomial.mapEquiv _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
      ).toCommRingCatIso
  let e₂ : CommRingCat.of (MvPolynomial {j // j ≠ β} k) ≅
      CommRingCat.of (HomogeneousLocalization.Away 𝒮 (MvPolynomial.X β)) :=
    (chartAwayEquiv k β).symm.toCommRingCatIso
  let e₃ := Proj.basicOpenIsoAway 𝒮 (MvPolynomial.X β) (X_mem_homogeneousSubmodule_one k β)
    Nat.one_pos
  let eB : CommRingCat.of (MvPolynomial {j // j ≠ β} Γ(Spec (CommRingCat.of k), ⊤)) ≅
      Γ(projectiveSpaceScheme k n, Proj.basicOpen 𝒮 (MvPolynomial.X β)) := e₁ ≪≫ e₂ ≪≫ e₃
  have heB : ∀ p, eB.hom p = Proj.awayToSection 𝒮 (MvPolynomial.X β)
      (chartOfPoly k β (MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom p)) :=
    fun p => rfl
  have hC : ∀ c, eB.hom (C c) = (dualProjectiveSpaceStructure k n).appLE ⊤
      (Proj.basicOpen 𝒮 (MvPolynomial.X β)) le_top c := by
    intro c
    rw [heB, MvPolynomial.map_C, chartOfPoly, coe_eval₂Hom, eval₂_C,
      ← bertiniChart_structure_appLE β, Iso.hom_inv_id_apply]
    rfl
  have hρ : ∀ j, eB.hom (bertiniChartCoord β j) = dualChartRatio k n β j := by
    intro j
    rw [heB, bertiniChartCoord, dualChartRatio]
    by_cases hj : j = β
    · subst hj
      rw [dif_pos rfl, map_one, map_one, chartRatio_self, map_one]
    · rw [dif_neg hj, MvPolynomial.map_X, chartOfPoly, coe_eval₂Hom, eval₂_X]
  exact bertiniChart_general q μ β (dualProjectiveSpaceStructure k n) hV hD
    (dualChartRatio k n β) eB hC hρ

end Chart

section Structure

/-- On a nonempty affine open `V` of an integral scheme of finite type over `k` of dimension `r`,
the ring `Γ(X, V)` is Noetherian of Krull dimension `r`. -/
private theorem bertiniChart_ringFacts [IsIntegral X] (hq : FiniteType q) (hV : IsAffineOpen V)
    [Nonempty V] (hr : topologicalKrullDim X = r) :
    IsNoetherianRing Γ(X, V) ∧ ringKrullDim Γ(X, V) = r := by
  obtain ⟨_, _⟩ := DimensionCodimension.exists_algebra_finiteType q hq V hV
  refine ⟨Algebra.FiniteType.isNoetherianRing k _, ?_⟩
  obtain ⟨N, hN, hNX⟩ := DimensionCodimension.exists_ringKrullDim_eq q hq V hV
  rw [hN, ← hNX, hr]

/-- **Structure of the chart incidence locus.** Let `X` be an integral scheme of finite type over
`k` of dimension `r < n`, let `V ⊆ X` be a nonempty affine open, and suppose that the columns
`J ℓ'` of the matrix `μ` form an invertible matrix over `Γ(X, V)` while `β ∉ J`. Then the common
zero locus of the functions `τ_ℓ = ∑ⱼ μ_{ℓ j} a_j / a_β` in the chart `V ×_k D₊(a_β)` is
irreducible of dimension `n - 1`: it is homeomorphic to the spectrum of a polynomial ring over
`Γ(X, V)` in `n - r - 1` variables. -/
theorem chartIncidence_isIrreducible_and_topologicalKrullDim [IsIntegral X] (hq : FiniteType q)
    (hV : IsAffineOpen V) [Nonempty V] (hr : topologicalKrullDim X = r) (hrn : r < n)
    (J : Fin (r + 1) ↪ Fin (n + 1)) (hdet : IsUnit (Matrix.of fun ℓ ℓ' => μ ℓ (J ℓ')).det)
    (hβ : β ∉ Set.range J) :
    IsIrreducible (chartIncidence q μ β) ∧
      topologicalKrullDim (chartIncidence q μ β) = ((n - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  obtain ⟨hnoeth, hdim⟩ := bertiniChart_ringFacts q hq hV hr
  obtain ⟨R, G, τ', e, hG, hrange, hbasic, he⟩ := bertiniChart_exists_chart q μ β hV
  let I : Ideal R := Ideal.span (Set.range τ')
  have hI : bertiniChartIdeal μ β = I.map (e : R →+* MvPolynomial {j // j ≠ β} Γ(X, V)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    refine congrArg (fun f => Ideal.span (Set.range f)) ?_
    funext ℓ
    exact (he ℓ).symm
  let eQ : (R ⧸ I) ≃+* MvPolynomial (BertiniFreeIdx β J) Γ(X, V) :=
    (Ideal.quotientEquiv I (bertiniChartIdeal μ β) e hI).trans
      (bertiniQuotEquiv hdet hβ).toRingEquiv
  have : IsDomain (R ⧸ I) := MulEquiv.isDomain _ eQ.toMulEquiv
  let h : PrimeSpectrum (R ⧸ I) → incidenceAmbient q n :=
    fun p => G (PrimeSpectrum.comap (Ideal.Quotient.mk I) p)
  have hemb : Topology.IsEmbedding h :=
    G.isOpenEmbedding.isEmbedding.comp
      (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (S := R ⧸ I)
        (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).isEmbedding
  have hτI : ∀ ℓ, τ' ℓ ∈ I := fun ℓ => Ideal.subset_span ⟨ℓ, rfl⟩
  have hrng : Set.range h = chartIncidence q μ β := by
    ext z
    simp only [chartIncidence, Set.mem_sdiff, Set.mem_iUnion, not_exists, SetLike.mem_coe]
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨?_, fun ℓ => ?_⟩
      · change _ ∈ (incidenceChart q V β : Set (incidenceAmbient q n))
        rw [← hrange]
        exact ⟨_, rfl⟩
      · intro hmem
        refine (hbasic ℓ _).1 hmem ?_
        change Ideal.Quotient.mk I (τ' ℓ) ∈ p.asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.2 (hτI ℓ)]
        exact p.asIdeal.zero_mem
    · rintro ⟨hz, hzτ⟩
      have hz' : z ∈ Set.range G := by rw [hrange]; exact hz
      obtain ⟨w, rfl⟩ := hz'
      have hw : w ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
        rw [range_comap_of_surjective (S := R ⧸ I) (f := Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective, Ideal.mk_ker]
        refine (PrimeSpectrum.mem_zeroLocus (w : PrimeSpectrum R) _).2 ?_
        rw [SetLike.coe_subset_coe]
        refine Ideal.span_le.2 (Set.range_subset_iff.2 fun ℓ => ?_)
        have := hzτ ℓ
        rwa [hbasic, not_not] at this
      obtain ⟨p, hp⟩ := hw
      exact ⟨p, by simp only [h, hp]⟩
  refine ⟨?_, ?_⟩
  · rw [← hrng, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image h hemb.continuous.continuousOn
  · rw [← hrng, ← IsHomeomorph.topologicalKrullDim_eq _ hemb.toHomeomorph.isHomeomorph,
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_of_ringEquiv eQ,
      bertiniChart_ringKrullDim_mvPolynomial, hdim, bertiniFreeIdx_card β J hβ, ← Nat.cast_add]
    congr 1
    omega

end Structure

end BertiniIncidence

end Hartshorne
