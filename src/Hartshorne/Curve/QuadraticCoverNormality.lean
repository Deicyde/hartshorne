/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.LinearCombination

/-!
# Normality of square-root covers

Hartshorne, *Algebraic Geometry*, II, Exercise 6.4 (p. 147).

Let `k` be a field of characteristic different from two and `f ∈ k[x₁, …, xₙ]` a nonconstant
squarefree polynomial. Then `A = k[x₁, …, xₙ, z] / (z² - f)` is an integrally closed domain, and it
is the integral closure of `k[x₁, …, xₙ]` in the quadratic extension `K(√f)` of the fraction field
`K` of `k[x₁, …, xₙ]`.

The proof is carried out for an integrally closed domain `R` with fraction field `K`, in which `2`
is a unit and squarefree elements are radical (for example a unique factorization domain), and a
squarefree nonunit `f ∈ R`. Every element of `L = K[z] / (z² - f)` has the form `a + b z` with
`a, b ∈ K`. If it is integral over `R`, so is its conjugate `a - b z`, hence so are its trace `2a`
and norm `a² - b² f`, which therefore lie in `R`. Then `(2b)² f ∈ R`, so `2b f` is integral over
`R` and lies in `R`; since `f` divides `(2b f)²` and is squarefree, it divides `2b f`, so `2b ∈ R`.
As `2` is a unit, `a, b ∈ R`. The comparison map `R[z] / (z² - f) → L` is injective, `L` is a field
because `f` is not a square in `K`, and the remaining assertions follow formally.
-/

open Polynomial

namespace Hartshorne
namespace QuadraticCover

section Ring
variable {S : Type*} [CommRing S] (a : S)

/-- Every element of `S[z]/(z² - a)` has the form `u + v z`. -/
theorem exists_eq_add_mul_root (x : AdjoinRoot (X ^ 2 - C a : S[X])) :
    ∃ u v : S, x = AdjoinRoot.of _ u + AdjoinRoot.of _ v * AdjoinRoot.root _ := by
  have hm : (X ^ 2 - C a : S[X]).Monic := monic_X_pow_sub_C a two_ne_zero
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    set r := p %ₘ (X ^ 2 - C a) with hr
    have hrdeg : r.degree ≤ 1 := by
      rcases subsingleton_or_nontrivial S with hS | hS
      · simp [Subsingleton.elim r 0]
      have hdeg : (X ^ 2 - C a : S[X]).degree = 2 := by
        rw [degree_X_pow_sub_C two_pos]; rfl
      have := degree_modByMonic_lt p hm
      rw [hdeg] at this
      exact Order.le_of_lt_succ this
    refine ⟨r.coeff 0, r.coeff 1, ?_⟩
    have h1 : AdjoinRoot.mk (X ^ 2 - C a) p = AdjoinRoot.mk (X ^ 2 - C a) r := by
      rw [AdjoinRoot.mk_eq_mk, hr, modByMonic_eq_sub_mul_div p (X ^ 2 - C a)]
      exact ⟨p /ₘ (X ^ 2 - C a), by ring⟩
    rw [h1, eq_X_add_C_of_degree_le_one hrdeg]
    simp [add_comm, AdjoinRoot.mk_C]

/-- The conjugation `z ↦ -z` of `S[z]/(z² - a)`. -/
noncomputable def conj : AdjoinRoot (X ^ 2 - C a : S[X]) →ₐ[S] AdjoinRoot (X ^ 2 - C a : S[X]) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId S _) (-AdjoinRoot.root _) (by
    have := AdjoinRoot.eval₂_root (X ^ 2 - C a : S[X])
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at this ⊢
    simpa [neg_sq] using this)

theorem conj_apply (u v : S) :
    conj a (AdjoinRoot.of _ u + AdjoinRoot.of _ v * AdjoinRoot.root _) =
      AdjoinRoot.of _ u - AdjoinRoot.of _ v * AdjoinRoot.root _ := by
  simp [conj, sub_eq_add_neg, AdjoinRoot.algebraMap_eq]

theorem root_sq : (AdjoinRoot.root (X ^ 2 - C a : S[X])) ^ 2 = AdjoinRoot.of _ a := by
  have := AdjoinRoot.eval₂_root (X ^ 2 - C a : S[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at this
  exact sub_eq_zero.mp this

end Ring

section Field
variable {K : Type*} [Field K] (c : K)

theorem degree_X_sq_sub_C : (X ^ 2 - C c : K[X]).degree = 2 := by
  rw [degree_X_pow_sub_C two_pos]; rfl

/-- Over a field, `1, z` are linearly independent in `K[z]/(z² - c)`. -/
theorem of_add_of_mul_root_eq_zero {u v : K}
    (h : AdjoinRoot.of (X ^ 2 - C c) u + AdjoinRoot.of _ v * AdjoinRoot.root _ = 0) :
    u = 0 ∧ v = 0 := by
  have h' : AdjoinRoot.mk (X ^ 2 - C c) (C u + C v * X) = 0 := by
    simpa [AdjoinRoot.mk_C] using h
  rw [AdjoinRoot.mk_eq_zero] at h'
  have h0 : C u + C v * X = 0 := by
    refine eq_zero_of_dvd_of_degree_lt h' ?_
    rw [degree_X_sq_sub_C]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt degree_C_le (by decide)
    · exact lt_of_le_of_lt (degree_C_mul_X_le v) (by decide)
  have h1 := congrArg (coeff · 0) h0
  have h2 := congrArg (coeff · 1) h0
  simp at h1 h2
  exact ⟨h1, h2⟩

theorem of_injective : Function.Injective (AdjoinRoot.of (X ^ 2 - C c : K[X])) :=
  AdjoinRoot.of.injective_of_degree_ne_zero (by rw [degree_X_sq_sub_C]; decide)

end Field

section Domain
variable {R : Type*} [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (f : R)

/-- The comparison map `R[z]/(z² - f) → K[z]/(z² - f)`. -/
noncomputable def toField :
    AdjoinRoot (X ^ 2 - C f : R[X]) →ₐ[R] AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X]) :=
  AdjoinRoot.mapAlgHom (Algebra.ofId R K) _ _ (by simp)

omit [IsDomain R] [IsFractionRing R K] in
theorem toField_apply (u v : R) :
    toField K f (AdjoinRoot.of _ u + AdjoinRoot.of _ v * AdjoinRoot.root _) =
      AdjoinRoot.of _ (algebraMap R K u) + AdjoinRoot.of _ (algebraMap R K v) *
        AdjoinRoot.root _ := by
  simp [toField]

omit [IsDomain R] in
theorem toField_injective : Function.Injective (toField K f) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨u, v, rfl⟩ := exists_eq_add_mul_root f x
  rw [toField_apply] at hx
  obtain ⟨hu, hv⟩ := of_add_of_mul_root_eq_zero _ hx
  rw [(IsFractionRing.injective R K).eq_iff' (map_zero _)] at hu hv
  simp [hu, hv]

/-- The key step: an element of `K[z]/(z² - f)` is integral over `R` exactly when it comes from
`R[z]/(z² - f)`. -/
theorem isIntegral_iff_exists_toField [IsIntegrallyClosed R] [DecompositionMonoid R]
    (hf : Squarefree f) (h2 : IsUnit (2 : R)) (x : AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X])) :
    IsIntegral R x ↔ ∃ y, toField K f y = x := by
  constructor
  · intro hx
    obtain ⟨a, b, hab⟩ := exists_eq_add_mul_root (algebraMap R K f) x
    subst hab
    have hK : ∀ t : K, IsIntegral R (AdjoinRoot.of (X ^ 2 - C (algebraMap R K f)) t) →
        ∃ r : R, algebraMap R K r = t :=
      fun t ht => IsIntegrallyClosed.isIntegral_iff.mp
        ((isIntegral_algHom_iff (IsScalarTower.toAlgHom R K _) (of_injective _)).mp ht)
    have hσ := hx.map ((conj (algebraMap R K f)).restrictScalars R)
    rw [AlgHom.coe_restrictScalars', conj_apply] at hσ
    obtain ⟨α, hα⟩ := hK (2 * a) (by
      convert hx.add hσ using 1; simp only [map_mul, map_ofNat]; ring)
    obtain ⟨β, hβ⟩ := hK (a ^ 2 - b ^ 2 * algebraMap R K f) (by
      convert hx.mul hσ using 1
      simp only [map_sub, map_mul, map_pow]
      linear_combination (AdjoinRoot.of _ b) ^ 2 * root_sq (algebraMap R K f))
    have hγ : algebraMap R K (α ^ 2 - 4 * β) = (2 * b) ^ 2 * algebraMap R K f := by
      simp only [map_sub, map_mul, map_pow, map_ofNat, hα, hβ]; ring
    obtain ⟨e, he⟩ : ∃ e : R, algebraMap R K e = 2 * b * algebraMap R K f := by
      refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 - C ((α ^ 2 - 4 * β) * f),
        monic_X_pow_sub_C _ two_ne_zero, ?_⟩
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, map_mul, hγ]; ring
    have hdvd : f ∣ e := hf.isRadical 2 e ⟨α ^ 2 - 4 * β, by
      apply IsFractionRing.injective R K
      simp only [map_pow, map_mul, he, hγ]; ring⟩
    obtain ⟨d, rfl⟩ := hdvd
    have hc0 : algebraMap R K f ≠ 0 := by
      simpa using (IsFractionRing.injective R K).ne hf.ne_zero
    have hd : algebraMap R K d = 2 * b := by
      rw [map_mul] at he
      apply mul_left_cancel₀ hc0
      rw [he]; ring
    have hu : algebraMap R K (h2.unit⁻¹ : Rˣ) * 2 = 1 := by
      rw [← map_ofNat (algebraMap R K) 2, ← map_mul]
      simp
    refine ⟨AdjoinRoot.of _ (α * (h2.unit⁻¹ : Rˣ)) + AdjoinRoot.of _ (d * (h2.unit⁻¹ : Rˣ)) *
      AdjoinRoot.root _, ?_⟩
    have e1 : algebraMap R K (α * (h2.unit⁻¹ : Rˣ)) = a := by
      rw [map_mul, hα]; linear_combination a * hu
    have e2 : algebraMap R K (d * (h2.unit⁻¹ : Rˣ)) = b := by
      rw [map_mul, hd]; linear_combination b * hu
    rw [toField_apply, e1, e2]
  · rintro ⟨y, rfl⟩
    have hm : (X ^ 2 - C f : R[X]).Monic := monic_X_pow_sub_C f two_ne_zero
    have := (AdjoinRoot.powerBasis' hm).finite
    exact (Algebra.IsIntegral.isIntegral y).map (toField K f)


omit [IsDomain R] in
/-- A squarefree nonunit of an integrally closed domain is not a square in the fraction field. -/
theorem irreducible_X_sq_sub_C [IsIntegrallyClosed R] (hf : Squarefree f) (hfu : ¬IsUnit f) :
    Irreducible (X ^ 2 - C (algebraMap R K f) : K[X]) := by
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => ?_
  obtain ⟨s, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (⟨X ^ 2 - C f, monic_X_pow_sub_C _ two_ne_zero, by simp [hb]⟩ : IsIntegral R b)
  have hs : s ^ 2 = f := IsFractionRing.injective R K (by simpa using hb)
  exact hfu (hs ▸ (hf s ⟨1, by rw [← hs]; ring⟩).pow 2)

/-- The general form of the result: over an integrally closed domain `R` in which `2` is a unit
and every squarefree element is radical, `R[z]/(z² - f)` is an integrally closed domain for a
squarefree nonunit `f`, with fraction field `K[z]/(z² - f)`, and it is the integral closure of `R`
in that field. -/
theorem isIntegrallyClosed_and_isIntegralClosure [IsIntegrallyClosed R] [DecompositionMonoid R]
    (hf : Squarefree f) (hfu : ¬IsUnit f) (h2 : IsUnit (2 : R)) :
    letI := (toField K f).toAlgebra
    IsDomain (AdjoinRoot (X ^ 2 - C f : R[X])) ∧
      IsIntegrallyClosed (AdjoinRoot (X ^ 2 - C f : R[X])) ∧
      IsField (AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X])) ∧
      IsFractionRing (AdjoinRoot (X ^ 2 - C f : R[X]))
        (AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X])) ∧
      IsIntegralClosure (AdjoinRoot (X ^ 2 - C f : R[X])) R
        (AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X])) := by
  let := (toField K f).toAlgebra
  have : Fact (Irreducible (X ^ 2 - C (algebraMap R K f) : K[X])) :=
    ⟨irreducible_X_sq_sub_C K f hf hfu⟩
  have : IsScalarTower R (AdjoinRoot (X ^ 2 - C f : R[X]))
      (AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X])) :=
    IsScalarTower.of_algebraMap_eq fun r => ((toField K f).commutes r).symm
  have hdom : IsDomain (AdjoinRoot (X ^ 2 - C f : R[X])) :=
    Function.Injective.isDomain (toField K f).toRingHom (toField_injective K f)
  have hic : IsIntegralClosure (AdjoinRoot (X ^ 2 - C f : R[X])) R
      (AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X])) :=
    ⟨toField_injective K f, fun {x} => isIntegral_iff_exists_toField K f hf h2 x⟩
  have : FiniteDimensional K (AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X])) :=
    (AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero two_pos _)).finite
  have hfr := IsIntegralClosure.isFractionRing_of_finite_extension R K
    (AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X])) (AdjoinRoot (X ^ 2 - C f : R[X]))
  refine ⟨hdom, ?_, Field.toIsField _, hfr, hic⟩
  have hm : (X ^ 2 - C f : R[X]).Monic := monic_X_pow_sub_C f two_ne_zero
  have := (AdjoinRoot.powerBasis' hm).finite
  exact (isIntegrallyClosed_iff (AdjoinRoot (X ^ 2 - C (algebraMap R K f) : K[X]))).mpr
    fun hx => IsIntegralClosure.isIntegral_iff.mp (isIntegral_trans (R := R) _ hx)

end Domain

end QuadraticCover

section Polynomial

variable {k : Type*} [Field k] {n : ℕ}

/-- The square-root cover algebra `A = k[x₁, …, xₙ, z] / (z² - f)`, presented as the quotient of
the polynomial ring in `z` over `k[x₁, …, xₙ]`. -/
abbrev SquareRootCover (f : MvPolynomial (Fin n) k) : Type _ :=
  AdjoinRoot (X ^ 2 - C f : (MvPolynomial (Fin n) k)[X])

/-- The quadratic extension `K(√f) = K[z] / (z² - f)` of the fraction field `K` of
`k[x₁, …, xₙ]` obtained by adjoining a square root of `f`. -/
abbrev SquareRootCoverField (f : MvPolynomial (Fin n) k) : Type _ :=
  AdjoinRoot (X ^ 2 - C (algebraMap (MvPolynomial (Fin n) k)
    (FractionRing (MvPolynomial (Fin n) k)) f) : (FractionRing (MvPolynomial (Fin n) k))[X])

/-- The evident map `A → K(√f)`, the identity on `k[x₁, …, xₙ]` and sending `z` to `√f`. -/
noncomputable instance (f : MvPolynomial (Fin n) k) :
    Algebra (SquareRootCover f) (SquareRootCoverField f) :=
  (QuadraticCover.toField (FractionRing (MvPolynomial (Fin n) k)) f).toAlgebra

instance (f : MvPolynomial (Fin n) k) :
    IsScalarTower (MvPolynomial (Fin n) k) (SquareRootCover f) (SquareRootCoverField f) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    ((QuadraticCover.toField (FractionRing (MvPolynomial (Fin n) k)) f).commutes r).symm

/-- **Hartshorne II, Exercise 6.4.** Let `k` be a field of characteristic different from two and
`f ∈ k[x₁, …, xₙ]` a nonconstant squarefree polynomial. Then `A = k[x₁, …, xₙ, z] / (z² - f)` is
an integrally closed domain; more precisely, `K(√f) = K[z] / (z² - f)` (with `K` the fraction
field of `k[x₁, …, xₙ]`) is a field, it is the fraction field of `A`, and `A` is the integral
closure of `k[x₁, …, xₙ]` in it. -/
theorem squareRootCover_isIntegrallyClosed (hk : ringChar k ≠ 2) {f : MvPolynomial (Fin n) k}
    (hf : Squarefree f) (hfc : 0 < f.totalDegree) :
    IsDomain (SquareRootCover f) ∧ IsIntegrallyClosed (SquareRootCover f) ∧
      IsField (SquareRootCoverField f) ∧
      IsFractionRing (SquareRootCover f) (SquareRootCoverField f) ∧
      IsIntegralClosure (SquareRootCover f) (MvPolynomial (Fin n) k) (SquareRootCoverField f) := by
  have hfu : ¬IsUnit f := fun h =>
    hfc.ne' (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp h).2
  have h2 : IsUnit (2 : MvPolynomial (Fin n) k) := by
    have : (2 : MvPolynomial (Fin n) k) = MvPolynomial.C 2 := (map_ofNat MvPolynomial.C 2).symm
    rw [this]
    exact (Ne.isUnit (Ring.two_ne_zero hk)).map MvPolynomial.C
  exact QuadraticCover.isIntegrallyClosed_and_isIntegralClosure
    (FractionRing (MvPolynomial (Fin n) k)) f hf hfu h2

end Polynomial
end Hartshorne
