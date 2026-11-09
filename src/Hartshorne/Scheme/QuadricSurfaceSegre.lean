/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuadricSurface
import Hartshorne.Scheme.ProjSurjectionClosedImmersion
import Hartshorne.Scheme.ProjClosedSubschemeTruncation

/-!
# The split quadric surface in `ℙ³`

Let `k` be a field and `Q = Proj` of the Segre ring (`Hartshorne.quadricSurface k`). The graded
`k`-algebra homomorphism `k[x, y, z, w] → ` Segre ring, `x, y, z, w ↦ s₀u₀, s₁u₁, s₀u₁, s₁u₀`
(`Hartshorne.quadricCoordinateHom`), is surjective, with kernel the ideal `(xy - zw)`
(`Hartshorne.ker_quadricCoordinateAlgHom`), so the Segre ring is `k[x, y, z, w] / (xy - zw)`
(`Hartshorne.quadricQuotientEquiv`). The graded surjection induces a closed immersion
`Q → ℙ³_k = Proj k[x, y, z, w]` (`Hartshorne.quadricSurfaceι`).

As a graded isomorphism (`Hartshorne.quadricQuotientHom`), this identifies `Q` with the closed
subscheme `V(xy - zw) = Proj k[x, y, z, w] / (xy - zw)` of `ℙ³_k` given by the homogeneous ideal
`(xy - zw)` (`Hartshorne.quadricIdeal`): `Hartshorne.projQuadricQuotientIso` and
`Hartshorne.projQuadricQuotientIso_hom_comp_quadricSurfaceι` (over `ℙ³_k`), and
`Hartshorne.ker_quadricSurfaceι` (equal ideal sheaves).

The kernel is computed with a normal form: modulo `xy - zw` every monomial is congruent to one
not divisible by `xy`, and sending each monomial `s^e u^g` of the Segre ring to the normal-form
monomial with that image gives an additive section `σ` with `σ(φ(P)) ≡ P` modulo `xy - zw`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra MvPolynomial

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "𝒬" => quadricGrading k

local notation "𝒮" => homogeneousSubmodule (Fin (3 + 1)) k

/-- The four coordinates `x, y, z, w = s₀u₀, s₁u₁, s₀u₁, s₁u₀` of `ℙ³` on `Q`. -/
def quadricCoordinates : Fin (3 + 1) → QuadricRing k :=
  ![quadricChart k 0 0, quadricChart k 1 1, quadricChart k 0 1, quadricChart k 1 0]

theorem quadricCoordinates_mem (l : Fin (3 + 1)) : quadricCoordinates k l ∈ 𝒬 1 := by
  fin_cases l <;> exact quadricChart_mem k _ _

/-- The `k`-algebra homomorphism `k[x, y, z, w] → ` Segre ring, `x, y, z, w ↦ s₀u₀, s₁u₁, s₀u₁,
s₁u₀`. -/
def quadricCoordinateAlgHom : MvPolynomial (Fin (3 + 1)) k →ₐ[k] QuadricRing k :=
  aeval (quadricCoordinates k)

theorem quadricCoordinateAlgHom_X (l : Fin (3 + 1)) :
    quadricCoordinateAlgHom k (X l) = quadricCoordinates k l :=
  aeval_X _ _

/-- The coordinate homomorphism preserves degrees. -/
theorem quadricCoordinateAlgHom_mem {d : ℕ} {p : MvPolynomial (Fin (3 + 1)) k} (hp : p ∈ 𝒮 d) :
    quadricCoordinateAlgHom k p ∈ 𝒬 d := by
  rw [mem_homogeneousSubmodule] at hp
  rw [p.as_sum, map_sum]
  refine sum_mem fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have h : Finsupp.degree m = d := by
      rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
      exact hp (mem_support_iff.1 hm)
    exact h
  rw [quadricCoordinateAlgHom, aeval_monomial]
  have h0 : algebraMap k (QuadricRing k) (coeff m p) ∈ 𝒬 0 := SetLike.algebraMap_mem_graded _ _
  have h1 : (m.prod fun j e => quadricCoordinates k j ^ e) ∈ 𝒬 d := by
    have := SetLike.prod_pow_mem_graded 𝒬 (F := m.support) (g := quadricCoordinates k)
      (i := fun _ => 1) m (fun j _ => quadricCoordinates_mem k j)
    rw [Finsupp.prod, ← hdeg]
    simpa using this
  simpa using SetLike.mul_mem_graded h0 h1

/-- The graded homomorphism `k[x, y, z, w] → ` Segre ring. -/
def quadricCoordinateHom : 𝒮 →+*ᵍ 𝒬 where
  __ := (quadricCoordinateAlgHom k).toRingHom
  map_mem hp := quadricCoordinateAlgHom_mem k hp

theorem quadricCoordinateHom_apply (p : MvPolynomial (Fin (3 + 1)) k) :
    quadricCoordinateHom k p = quadricCoordinateAlgHom k p :=
  rfl

theorem quadricChart_mem_range (i j : Fin 2) :
    quadricChart k i j ∈ (quadricCoordinateAlgHom k).range := by
  fin_cases i <;> fin_cases j
  · exact ⟨X 0, quadricCoordinateAlgHom_X k 0⟩
  · exact ⟨X 2, quadricCoordinateAlgHom_X k 2⟩
  · exact ⟨X 3, quadricCoordinateAlgHom_X k 3⟩
  · exact ⟨X 1, quadricCoordinateAlgHom_X k 1⟩

theorem single_mem_range_quadricCoordinateAlgHom (c : k) :
    ∀ (d : ℕ) (p : quadricExponents), quadricDegree p = d →
      single p c ∈ (quadricCoordinateAlgHom k).range := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have h1 := quadricDegree_apply p
    have h2 := quadricDegree_eq_snd p
    have hp0 : p = 0 := by
      apply Subtype.ext
      apply Prod.ext <;> funext l <;> fin_cases l <;> simp <;> omega
    subst hp0
    exact ⟨C c, (aeval_C (quadricCoordinates k) c).trans rfl⟩
  | succ d ih =>
    intro p hp
    have h1 := quadricDegree_apply p
    have h2 := quadricDegree_eq_snd p
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, 0 < p.1.1 i := by
      by_contra! h
      have := h 0; have := h 1; omega
    obtain ⟨j, hj⟩ : ∃ j : Fin 2, 0 < p.1.2 j := by
      by_contra! h
      have := h 0; have := h 1; omega
    let q : quadricExponents := ⟨(p.1.1 - Pi.single i 1, p.1.2 - Pi.single j 1), by
      rw [mem_quadricExponents]
      fin_cases i <;> fin_cases j <;> simp at hi hj ⊢ <;> omega⟩
    have hqp : quadricChartExp i j + q = p := by
      apply Subtype.ext
      apply Prod.ext <;> funext l <;>
        fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [q, quadricChartExp] at hi hj ⊢ <;>
        omega
    have hq : quadricDegree q = d := by
      rw [← hqp, map_add, quadricDegree_chartExp] at hp
      omega
    have : single p c = quadricChart k i j * single q c := by
      rw [quadricChart, single_mul_single, one_mul, hqp]
    rw [this]
    exact mul_mem (quadricChart_mem_range k i j) (ih q hq)

/-- The coordinate homomorphism is surjective: the Segre ring is generated by `s₀u₀, s₁u₁, s₀u₁,
s₁u₀`. -/
theorem quadricCoordinateAlgHom_surjective : Function.Surjective (quadricCoordinateAlgHom k) := by
  intro a
  rw [← sum_coeff_single a, Finsupp.sum]
  exact sum_mem fun p _ => single_mem_range_quadricCoordinateAlgHom k _ _ p rfl

theorem quadricCoordinateHom_surjective : Function.Surjective (quadricCoordinateHom k) :=
  quadricCoordinateAlgHom_surjective k

/-- The irrelevant ideal of the Segre ring is generated by the image of that of
`k[x, y, z, w]`. -/
theorem irrelevant_le_map_quadricCoordinateHom :
    HomogeneousIdeal.irrelevant 𝒬 ≤
      (HomogeneousIdeal.irrelevant 𝒮).map (quadricCoordinateHom k) := by
  change (HomogeneousIdeal.irrelevant 𝒬).toIdeal ≤
    (HomogeneousIdeal.irrelevant 𝒮).toIdeal.map (quadricCoordinateHom k)
  refine (quadric_irrelevant_le_span k).trans (Ideal.span_le.mpr ?_)
  have key : ∀ l : Fin (3 + 1), quadricCoordinates k l ∈
      (HomogeneousIdeal.irrelevant 𝒮).toIdeal.map (quadricCoordinateHom k) := fun l => by
    rw [← quadricCoordinateAlgHom_X]
    exact Ideal.mem_map_of_mem (quadricCoordinateHom k)
      (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem_homogeneousSubmodule_one k l))
  rintro _ ⟨⟨i, j⟩, rfl⟩
  fin_cases i <;> fin_cases j
  · exact key 0
  · exact key 2
  · exact key 3
  · exact key 1

/-- **The quadric in `ℙ³`.** The closed immersion `Q → ℙ³_k = Proj k[x, y, z, w]` induced by the
graded surjection `x, y, z, w ↦ s₀u₀, s₁u₁, s₀u₁, s₁u₀`. -/
def quadricSurfaceι : quadricSurface k ⟶ Proj 𝒮 :=
  Proj.map (quadricCoordinateHom k) (irrelevant_le_map_quadricCoordinateHom k)

instance quadricSurfaceι_isClosedImmersion : IsClosedImmersion (quadricSurfaceι k) := by
  have h := isClosedImmersion_projPartialMap_comp_top_of_surjective
    (quadricCoordinateHom_surjective k)
  rw [projPartialMap_eq_map (irrelevant_le_map_quadricCoordinateHom k), Scheme.homOfLE_ι_assoc,
    ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at h
  exact h

section Kernel

/-- The quadratic relation `xy - zw`. -/
def quadricRelation : MvPolynomial (Fin (3 + 1)) k := X 0 * X 1 - X 2 * X 3

/-- The exponents of the coordinates `x, y, z, w = s₀u₀, s₁u₁, s₀u₁, s₁u₀`. -/
def quadricCoordinateExp : Fin (3 + 1) → quadricExponents :=
  ![quadricChartExp 0 0, quadricChartExp 1 1, quadricChartExp 0 1, quadricChartExp 1 0]

/-- The exponent of the image of the monomial `x^{m₀} y^{m₁} z^{m₂} w^{m₃}`. -/
def quadricMonomialExp (m : Fin (3 + 1) →₀ ℕ) : quadricExponents :=
  m 0 • quadricCoordinateExp 0 + m 1 • quadricCoordinateExp 1 + m 2 • quadricCoordinateExp 2 +
    m 3 • quadricCoordinateExp 3

theorem quadricMonomialExp_apply (m : Fin (3 + 1) →₀ ℕ) :
    (quadricMonomialExp m).1.1 0 = m 0 + m 2 ∧ (quadricMonomialExp m).1.1 1 = m 1 + m 3 ∧
      (quadricMonomialExp m).1.2 0 = m 0 + m 3 ∧ (quadricMonomialExp m).1.2 1 = m 1 + m 2 := by
  simp [quadricMonomialExp, quadricCoordinateExp, quadricChartExp]

theorem quadricCoordinateAlgHom_monomial (m : Fin (3 + 1) →₀ ℕ) (c : k) :
    quadricCoordinateAlgHom k (monomial m c) = single (quadricMonomialExp m) c := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four, map_mul,
    map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, quadricCoordinateAlgHom_X,
    quadricCoordinateAlgHom_X, quadricCoordinateAlgHom_X, quadricCoordinateAlgHom_X,
    quadricCoordinateAlgHom, aeval_C]
  simp only [quadricCoordinates, quadricChart, Matrix.cons_val, single_pow, one_pow]
  rw [single_mul_single, single_mul_single, single_mul_single]
  change single 0 c * _ = _
  rw [single_mul_single, zero_add, mul_one, mul_one, mul_one, mul_one]
  rfl

/-- The normal-form exponent: the monomial not divisible by `xy` with image exponent `p`. -/
def quadricNormalExp (p : quadricExponents) : Fin (3 + 1) →₀ ℕ :=
  if p.1.2 1 ≤ p.1.1 0 then
    Finsupp.equivFunOnFinite.symm ![p.1.1 0 - p.1.2 1, 0, p.1.2 1, p.1.1 1]
  else Finsupp.equivFunOnFinite.symm ![0, p.1.2 1 - p.1.1 0, p.1.1 0, p.1.2 0]

theorem quadricRelation_mem_ker :
    quadricRelation k ∈ RingHom.ker (quadricCoordinateAlgHom k) := by
  rw [RingHom.mem_ker, quadricRelation, map_sub, map_mul, map_mul]
  simp only [quadricCoordinateAlgHom_X, quadricCoordinates, quadricChart, Matrix.cons_val, single_mul_single, mul_one]
  rw [sub_eq_zero]
  congr 1
  apply Subtype.ext
  apply Prod.ext <;> funext l <;> fin_cases l <;> simp [quadricChartExp]

theorem monomial_fin_four (m : Fin (3 + 1) →₀ ℕ) (c : k) :
    monomial m c = C c * (X 0 ^ m 0 * X 1 ^ m 1 * X 2 ^ m 2 * X 3 ^ m 3) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]

theorem quadricNormalExp_of_le (m : Fin (3 + 1) →₀ ℕ) (h : m 1 ≤ m 0) :
    quadricNormalExp (quadricMonomialExp m) =
      Finsupp.equivFunOnFinite.symm ![m 0 - m 1, 0, m 1 + m 2, m 1 + m 3] := by
  obtain ⟨h0, h1, h2, h3⟩ := quadricMonomialExp_apply m
  rw [quadricNormalExp, if_pos (by omega)]
  simp only [h0, h1, h3]
  rw [show m 0 + m 2 - (m 1 + m 2) = m 0 - m 1 by omega]

theorem quadricNormalExp_of_lt (m : Fin (3 + 1) →₀ ℕ) (h : m 0 < m 1) :
    quadricNormalExp (quadricMonomialExp m) =
      Finsupp.equivFunOnFinite.symm ![0, m 1 - m 0, m 0 + m 2, m 0 + m 3] := by
  obtain ⟨h0, h1, h2, h3⟩ := quadricMonomialExp_apply m
  rw [quadricNormalExp, if_neg (by omega)]
  simp only [h0, h2, h3]
  rw [show m 1 + m 2 - (m 0 + m 2) = m 1 - m 0 by omega]

theorem pow_sub_pow_mem_span_quadricRelation (t : ℕ) :
    (X 2 * X 3) ^ t - (X 0 * X 1) ^ t ∈ Ideal.span {quadricRelation k} := by
  have h : quadricRelation k = -(X 2 * X 3 - X 0 * X 1) := by
    rw [quadricRelation, neg_sub]
  rw [Ideal.mem_span_singleton, h, neg_dvd]
  exact sub_dvd_pow_sub_pow _ _ _

/-- Modulo `xy - zw`, every monomial is congruent to its normal form. -/
theorem monomial_normalExp_sub_mem (m : Fin (3 + 1) →₀ ℕ) (c : k) :
    monomial (quadricNormalExp (quadricMonomialExp m)) c - monomial m c ∈
      Ideal.span {quadricRelation k} := by
  by_cases h : m 1 ≤ m 0
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    rw [quadricNormalExp_of_le m h, monomial_fin_four, monomial_fin_four]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Matrix.cons_val]
    rw [show m 0 - m 1 = d by omega, hd]
    have key := Ideal.mul_mem_left _ (C c * X 0 ^ d * X 2 ^ m 2 * X 3 ^ m 3)
      (pow_sub_pow_mem_span_quadricRelation k (m 1))
    convert key using 1
    ring
  · push Not at h
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h.le
    rw [quadricNormalExp_of_lt m h, monomial_fin_four, monomial_fin_four]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Matrix.cons_val]
    rw [show m 1 - m 0 = d by omega, hd]
    have key := Ideal.mul_mem_left _ (C c * X 1 ^ d * X 2 ^ m 2 * X 3 ^ m 3)
      (pow_sub_pow_mem_span_quadricRelation k (m 0))
    convert key using 1
    ring

/-- The additive section of the coordinate homomorphism on monomials: `s^e u^g ↦` its normal
form monomial in `x, y, z, w`. -/
def quadricNormalSection : QuadricRing k →+ MvPolynomial (Fin (3 + 1)) k :=
  (Finsupp.liftAddHom fun p => (monomial (quadricNormalExp p)).toAddMonoidHom).comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem quadricNormalSection_single (p : quadricExponents) (c : k) :
    quadricNormalSection k (single p c) = monomial (quadricNormalExp p) c := by
  simp [quadricNormalSection, AddMonoidAlgebra.coeffAddEquiv]

/-- Every polynomial is congruent modulo `xy - zw` to the normal form of its image. -/
theorem quadricNormalSection_sub_mem (P : MvPolynomial (Fin (3 + 1)) k) :
    quadricNormalSection k (quadricCoordinateAlgHom k P) - P ∈ Ideal.span {quadricRelation k} := by
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [quadricCoordinateAlgHom_monomial, quadricNormalSection_single]
    exact monomial_normalExp_sub_mem k m c
  | add P Q hP hQ =>
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hP hQ

/-- **The homogeneous coordinate ring of the quadric.** The kernel of
`k[x, y, z, w] → ` Segre ring is the ideal `(xy - zw)`. -/
theorem ker_quadricCoordinateAlgHom :
    RingHom.ker (quadricCoordinateAlgHom k) = Ideal.span {quadricRelation k} := by
  refine le_antisymm (fun P hP => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr
    (quadricRelation_mem_ker k))
  have h := quadricNormalSection_sub_mem k P
  rw [RingHom.mem_ker.mp hP, map_zero, zero_sub] at h
  simpa using neg_mem h

/-- The homogeneous coordinate ring of `V(xy - zw) ⊆ ℙ³_k` is the Segre ring:
`k[x, y, z, w] / (xy - zw) ≅ ` Segre ring, `x, y, z, w ↦ s₀u₀, s₁u₁, s₀u₁, s₁u₀`. -/
def quadricQuotientEquiv :
    (MvPolynomial (Fin (3 + 1)) k ⧸ Ideal.span {quadricRelation k}) ≃ₐ[k] QuadricRing k :=
  (Ideal.quotientEquivAlgOfEq k (ker_quadricCoordinateAlgHom k)).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective (quadricCoordinateAlgHom_surjective k))

theorem quadricQuotientEquiv_mk (P : MvPolynomial (Fin (3 + 1)) k) :
    quadricQuotientEquiv k (Ideal.Quotient.mk _ P) = quadricCoordinateAlgHom k P :=
  rfl

end Kernel

section ClosedSubscheme

open ProjTruncation

/-- `xy - zw` is homogeneous of degree two. -/
theorem quadricRelation_mem : quadricRelation k ∈ 𝒮 2 :=
  sub_mem
    (SetLike.mul_mem_graded (X_mem_homogeneousSubmodule_one k 0)
      (X_mem_homogeneousSubmodule_one k 1))
    (SetLike.mul_mem_graded (X_mem_homogeneousSubmodule_one k 2)
      (X_mem_homogeneousSubmodule_one k 3))

/-- The homogeneous ideal `(xy - zw)` of `k[x, y, z, w]`. -/
def quadricIdeal : HomogeneousIdeal 𝒮 :=
  ⟨Ideal.span {quadricRelation k}, Ideal.homogeneous_span 𝒮 _ fun _ hx => by
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨2, quadricRelation_mem k⟩⟩

/-- The graded isomorphism `k[x, y, z, w] / (xy - zw) → ` Segre ring,
`x, y, z, w ↦ s₀u₀, s₁u₁, s₀u₁, s₁u₀`, with `k[x, y, z, w] / (xy - zw)` graded as a quotient. -/
def quadricQuotientHom : gradedQuotient 𝒮 (quadricIdeal k) →+*ᵍ 𝒬 where
  __ := (quadricQuotientEquiv k).toRingEquiv.toRingHom
  map_mem := by
    intro i x hx
    obtain ⟨a, ha, rfl⟩ := mem_gradedQuotient_iff.mp hx
    exact quadricCoordinateAlgHom_mem k ha

theorem quadricQuotientHom_mk (P : MvPolynomial (Fin (3 + 1)) k) :
    quadricQuotientHom k (Ideal.Quotient.mk _ P) = quadricCoordinateAlgHom k P :=
  rfl

theorem quadricQuotientHom_surjective : Function.Surjective (quadricQuotientHom k) :=
  (quadricQuotientEquiv k).surjective

/-- The graded isomorphism is bijective in every degree. -/
theorem quadricQuotientHom_bijective (d : ℕ) :
    Function.Bijective ((quadricQuotientHom k).gradedAddHom d) := by
  constructor
  · intro x y h
    exact Subtype.ext ((quadricQuotientEquiv k).injective (congrArg Subtype.val h))
  · intro y
    obtain ⟨a, ha⟩ := quadricCoordinateAlgHom_surjective k y
    refine ⟨⟨Ideal.Quotient.mk _ (DirectSum.decompose 𝒮 a d : MvPolynomial (Fin (3 + 1)) k),
      mk_mem_gradedQuotient (DirectSum.decompose 𝒮 a d).2⟩, Subtype.ext ?_⟩
    rw [GradedRingHom.gradedAddHom_apply_coe]
    change quadricCoordinateHom k (DirectSum.decompose 𝒮 a d : MvPolynomial (Fin (3 + 1)) k) = y
    rw [GradedRingHom.map_directSumDecompose, quadricCoordinateHom_apply, ha,
      DirectSum.decompose_coe, DirectSum.of_eq_same]

theorem isIso_map_quadricQuotientHom :
    IsIso (Proj.map (quadricQuotientHom k)
      (irrelevant_le_map_of_surjective (quadricQuotientHom_surjective k))) := by
  have hiso : IsIso (projPartialMap (quadricQuotientHom k)) :=
    isIso_projPartialMap_of_bijective (d₀ := 0) fun d _ => quadricQuotientHom_bijective k d
  have hι : IsIso (projPartialDomain (quadricQuotientHom k)).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
    have hy : y ∈ projPartialDomain (quadricQuotientHom k) := by
      rw [projPartialDomain_eq_top_of_surjective (quadricQuotientHom_surjective k)]
      trivial
    exact ⟨⟨y, hy⟩, rfl⟩
  rw [projPartialMap_eq_map
    (irrelevant_le_map_of_surjective (quadricQuotientHom_surjective k))] at hiso
  exact IsIso.of_isIso_comp_left (projPartialDomain (quadricQuotientHom k)).ι _

/-- **`Q` is the closed subscheme `V(xy - zw) = Proj k[x, y, z, w] / (xy - zw)` of `ℙ³_k`**:
the isomorphism `Proj (k[x, y, z, w] / (xy - zw)) ≅ Q` induced by the graded isomorphism of
coordinate rings. -/
def projQuadricQuotientIso : Proj (gradedQuotient 𝒮 (quadricIdeal k)) ≅ quadricSurface k :=
  (@asIso _ _ _ _ (Proj.map (quadricQuotientHom k)
    (irrelevant_le_map_of_surjective (quadricQuotientHom_surjective k)))
    (isIso_map_quadricQuotientHom k)).symm

/-- The isomorphism `Proj (k[x, y, z, w] / (xy - zw)) ≅ Q` is compatible with the closed
immersions into `ℙ³_k`: the quadric `Q ⊆ ℙ³_k` is the closed subscheme cut out by `xy - zw`. -/
theorem projQuadricQuotientIso_hom_comp_quadricSurfaceι :
    (projQuadricQuotientIso k).hom ≫ quadricSurfaceι k = projQuotientι 𝒮 (quadricIdeal k) := by
  rw [projQuadricQuotientIso, Iso.symm_hom, Iso.inv_comp_eq, asIso_hom, projQuotientι_eq_map,
    ← Proj.map_comp, quadricSurfaceι]
  exact map_congr (GradedRingHom.ext fun _ => rfl) _ _

/-- The closed immersion `Q → ℙ³_k` has the ideal sheaf of `xy - zw`. -/
theorem ker_quadricSurfaceι :
    (quadricSurfaceι k).ker = (projQuotientι 𝒮 (quadricIdeal k)).ker := by
  rw [← projQuadricQuotientIso_hom_comp_quadricSurfaceι, Scheme.Hom.ker_comp_of_isIso]

end ClosedSubscheme

end Hartshorne
