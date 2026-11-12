/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Lengths over the homogeneous and the ordinary localization at a homogeneous prime

Let `A = ⊕ₙ Aₙ` be an `ℕ`-graded domain, `𝔮` a homogeneous prime and `f ∈ A₁ ∖ 𝔮`. Write
`A₍𝔮₎` for the degree-zero part of the homogeneous localization at `𝔮` (the local ring of `Proj A`
at `𝔮`) and `A_𝔮` for the ordinary localization.

The map `A₍𝔮₎[X] → A_𝔮`, `X ↦ f`, is injective (`injective_evalOverPow`), and `A_𝔮` is its
localization at the polynomials mapping to units: a homogeneous `a ∈ Aₙ` is `(a / fⁿ) · fⁿ`. Hence
`A_𝔮` is flat over `A₍𝔮₎` (`flat_atPrime`). The maximal ideal of `A₍𝔮₎` generates that of `A_𝔮`
(`map_maximalIdeal_atPrime`), because a homogeneous `a ∈ 𝔮 ∩ Aₙ` is `(a / fⁿ) · fⁿ` with
`a / fⁿ` in the maximal ideal of `A₍𝔮₎`. Consequently lengths do not change under
`A₍𝔮₎ → A_𝔮`: for every ideal `I` of `A₍𝔮₎`, `ℓ_{A_𝔮}(A_𝔮 / I A_𝔮) = ℓ_{A₍𝔮₎}(A₍𝔮₎ / I)`
(`length_quotient_map_atPrime`).
-/

namespace Hartshorne.GradedLocalizationLength

open HomogeneousLocalization Polynomial IsLocalRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜] (𝔮 : Ideal A) [𝔮.IsPrime]

/-- The element `a / fⁿ` of the homogeneous localization at `𝔮`, for `a ∈ Aₙ` and
`f ∈ A₁ ∖ 𝔮`. -/
noncomputable def overPow {f : A} (hf : f ∈ 𝒜 1) (hf𝔮 : f ∉ 𝔮) {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    HomogeneousLocalization.AtPrime 𝒜 𝔮 :=
  HomogeneousLocalization.mk
    ⟨d, ⟨a, ha⟩, ⟨f ^ d, by simpa using SetLike.pow_mem_graded d hf⟩,
      fun h ↦ hf𝔮 (‹𝔮.IsPrime›.mem_of_pow_mem d h)⟩

theorem overPow_val_mul_pow {f : A} (hf : f ∈ 𝒜 1) (hf𝔮 : f ∉ 𝔮) {d : ℕ} {a : A}
    (ha : a ∈ 𝒜 d) :
    (overPow 𝒜 𝔮 hf hf𝔮 ha).val * algebraMap A (Localization.AtPrime 𝔮) f ^ d =
      algebraMap A (Localization.AtPrime 𝔮) a := by
  rw [overPow, val_mk, ← map_pow, Localization.mk_eq_mk', IsLocalization.mk'_spec]

/-- The evaluation `A₍𝔮₎[X] → A_𝔮`, `X ↦ f`. -/
noncomputable def evalOverPow (f : A) :
    (HomogeneousLocalization.AtPrime 𝒜 𝔮)[X] →+* Localization.AtPrime 𝔮 :=
  eval₂RingHom (algebraMap _ _) (algebraMap A (Localization.AtPrime 𝔮) f)

theorem algebraMap_mem_range_evalOverPow {f : A} (hf : f ∈ 𝒜 1) (hf𝔮 : f ∉ 𝔮) (a : A) :
    algebraMap A (Localization.AtPrime 𝔮) a ∈ (evalOverPow 𝒜 𝔮 f).range := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  rw [map_sum]
  refine Subring.sum_mem _ fun d _ ↦ ⟨C (overPow 𝒜 𝔮 hf hf𝔮 (DirectSum.decompose 𝒜 a d).2) * X ^ d,
    ?_⟩
  rw [evalOverPow, map_mul, map_pow, coe_eval₂RingHom, eval₂_C, eval₂_X,
    HomogeneousLocalization.algebraMap_apply, overPow_val_mul_pow]

variable [IsDomain A]

/-- Over a graded domain, `f ∈ A₁ ∖ 𝔮` is transcendental over the homogeneous localization:
`A₍𝔮₎[X] → A_𝔮`, `X ↦ f`, is injective. -/
theorem injective_evalOverPow {f : A} (hf : f ∈ 𝒜 1) (hf𝔮 : f ∉ 𝔮) :
    Function.Injective (evalOverPow 𝒜 𝔮 f) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro P hP
  -- a common homogeneous denominator `t` of the coefficients
  set s := P.support
  let den : ℕ → A := fun d ↦ (P.coeff d).den
  let t : A := ∏ d ∈ s, den d
  have hden : ∀ d, den d ∉ 𝔮 := fun d ↦ (P.coeff d).den_mem
  have ht𝔮 : t ∉ 𝔮 := by
    intro h
    obtain ⟨d, -, hd⟩ := (Ideal.IsPrime.prod_mem_iff (hp := ‹_›)).mp h
    exact hden d hd
  let E : ℕ := ∑ d ∈ s, (P.coeff d).deg
  -- `c d = num_d ∏_{d' ≠ d} den_{d'}`, homogeneous of degree `E`
  let c : ℕ → A := fun d ↦ (P.coeff d).num * ∏ d' ∈ s.erase d, den d'
  have hc : ∀ d ∈ s, c d ∈ 𝒜 E := by
    intro d hd
    have hE : E = (P.coeff d).deg + ∑ d' ∈ s.erase d, (P.coeff d').deg := by
      exact (Finset.add_sum_erase s _ hd).symm
    rw [hE]
    exact SetLike.mul_mem_graded (P.coeff d).num_mem_deg
      (SetLike.prod_mem_graded _ _ _ fun d' _ ↦ (P.coeff d').den_mem_deg)
  have htc : ∀ d ∈ s, algebraMap A (Localization.AtPrime 𝔮) t * (P.coeff d).val =
      algebraMap A (Localization.AtPrime 𝔮) (c d) := by
    intro d hd
    have h1 := (P.coeff d).den_smul_val
    rw [Algebra.smul_def] at h1
    have ht : t = den d * ∏ d' ∈ s.erase d, den d' := (Finset.mul_prod_erase s den hd).symm
    simp only [c, ht, map_mul]
    linear_combination (algebraMap A (Localization.AtPrime 𝔮) (∏ d' ∈ s.erase d, den d')) * h1
  -- `∑ c d fᵈ = 0` in `A`
  have hsum : ∑ d ∈ s, c d * f ^ d = 0 := by
    apply IsLocalization.injective (Localization.AtPrime 𝔮) 𝔮.primeCompl_le_nonZeroDivisors
    rw [map_zero, map_sum]
    have hP' : algebraMap A (Localization.AtPrime 𝔮) t * evalOverPow 𝒜 𝔮 f P = 0 := by
      rw [hP, mul_zero]
    rw [evalOverPow, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum] at hP'
    rw [← hP']
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [HomogeneousLocalization.algebraMap_apply, ← mul_assoc, htc d hd, map_mul, map_pow]
  -- comparing homogeneous components, each `c d fᵈ` vanishes
  have hcomp : ∀ d ∈ s, c d * f ^ d = 0 := by
    intro d hd
    have hmem : ∀ d' ∈ s, c d' * f ^ d' ∈ 𝒜 (E + d') := fun d' hd' ↦
      SetLike.mul_mem_graded (hc d' hd') (by simpa using SetLike.pow_mem_graded d' hf)
    have h := congrArg (fun x ↦ (DirectSum.decompose 𝒜 x (E + d) : A)) hsum
    simp only [DirectSum.decompose_sum, DirectSum.decompose_zero, DirectSum.zero_apply,
      ZeroMemClass.coe_zero] at h
    rw [DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_eq_single_of_mem d hd] at h
    · rwa [DirectSum.decompose_of_mem_same 𝒜 (hmem d hd)] at h
    · intro d' hd' hne
      rw [DirectSum.decompose_of_mem_ne 𝒜 (hmem d' hd')]
      omega
  ext d
  rw [coeff_zero]
  by_cases hd : d ∈ s
  · have hf0 : f ≠ 0 := fun h ↦ hf𝔮 (h ▸ 𝔮.zero_mem)
    have hcd : c d = 0 := by
      have := hcomp d hd
      rwa [mul_eq_zero, or_iff_left (pow_ne_zero d hf0)] at this
    have hval : algebraMap A (Localization.AtPrime 𝔮) t * (P.coeff d).val = 0 := by
      rw [htc d hd, hcd, map_zero]
    have hunit : IsUnit (algebraMap A (Localization.AtPrime 𝔮) t) :=
      IsLocalization.map_units _ (⟨t, ht𝔮⟩ : 𝔮.primeCompl)
    rw [hunit.mul_right_eq_zero] at hval
    rw [hval, HomogeneousLocalization.val_zero]
  · rw [notMem_support_iff.mp hd]

/-- Over a graded domain with an element `f ∈ A₁ ∖ 𝔮`, the ordinary localization `A_𝔮` is flat
over the homogeneous localization `A₍𝔮₎`: it is a localization of `A₍𝔮₎[X]` via `X ↦ f`. -/
theorem flat_atPrime {f : A} (hf : f ∈ 𝒜 1) (hf𝔮 : f ∉ 𝔮) :
    Module.Flat (HomogeneousLocalization.AtPrime 𝒜 𝔮) (Localization.AtPrime 𝔮) := by
  let φ := evalOverPow 𝒜 𝔮 f
  let _ : Algebra (AtPrime 𝒜 𝔮)[X] (Localization.AtPrime 𝔮) := φ.toAlgebra
  have : IsScalarTower (AtPrime 𝒜 𝔮) (AtPrime 𝒜 𝔮)[X] (Localization.AtPrime 𝔮) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = φ (Polynomial.C r)
      simp [φ, evalOverPow]
  let M : Submonoid (AtPrime 𝒜 𝔮)[X] := (IsUnit.submonoid (Localization.AtPrime 𝔮)).comap φ
  have : IsLocalization M (Localization.AtPrime 𝔮) := by
    rw [isLocalization_iff]
    refine ⟨fun m ↦ m.2, fun z ↦ ?_, fun {x y} h ↦ ⟨1, ?_⟩⟩
    · obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z
      obtain ⟨P, hP⟩ := algebraMap_mem_range_evalOverPow 𝒜 𝔮 hf hf𝔮 a
      obtain ⟨Q, hQ⟩ := algebraMap_mem_range_evalOverPow 𝒜 𝔮 hf hf𝔮 s
      refine ⟨⟨P, ⟨Q, ?_⟩⟩, ?_⟩
      · change IsUnit (φ Q)
        rw [hQ]
        exact IsLocalization.map_units _ s
      · change IsLocalization.mk' _ a s * φ Q = φ P
        rw [hQ, hP, IsLocalization.mk'_spec]
    · rw [injective_evalOverPow 𝒜 𝔮 hf hf𝔮 h]
  have := IsLocalization.flat (Localization.AtPrime 𝔮) M
  exact Module.Flat.trans _ (AtPrime 𝒜 𝔮)[X] _

instance isLocalHom_algebraMap_atPrime :
    IsLocalHom (algebraMap (HomogeneousLocalization.AtPrime 𝒜 𝔮) (Localization.AtPrime 𝔮)) :=
  ⟨fun a ha ↦ (isUnit_iff_isUnit_val 𝒜 𝔮 a).mp ha⟩

omit [IsDomain A] in
/-- The maximal ideal of `A₍𝔮₎` generates the maximal ideal of `A_𝔮`. -/
theorem map_maximalIdeal_atPrime (h𝔮 : 𝔮.IsHomogeneous 𝒜) {f : A} (hf : f ∈ 𝒜 1)
    (hf𝔮 : f ∉ 𝔮) :
    (maximalIdeal (HomogeneousLocalization.AtPrime 𝒜 𝔮)).map
        (algebraMap _ (Localization.AtPrime 𝔮)) =
      maximalIdeal (Localization.AtPrime 𝔮) := by
  classical
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h ↦ hx (isUnit_of_map_unit _ _ h)
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
    refine sum_mem fun d _ ↦ ?_
    have had : (DirectSum.decompose 𝒜 a d : A) ∈ 𝔮 := h𝔮 d ha
    rw [← overPow_val_mul_pow 𝒜 𝔮 hf hf𝔮 (DirectSum.decompose 𝒜 a d).2]
    refine Ideal.mul_mem_right _ _ (show algebraMap (AtPrime 𝒜 𝔮) (Localization.AtPrime 𝔮)
      (overPow 𝒜 𝔮 hf hf𝔮 (DirectSum.decompose 𝒜 a d).2) ∈ _ from Ideal.mem_map_of_mem _ ?_)
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := ((hu.map (algebraMap _ (Localization.AtPrime 𝔮))).mul
      ((IsLocalization.map_units (Localization.AtPrime 𝔮) (⟨f, hf𝔮⟩ : 𝔮.primeCompl)).pow d))
    rw [HomogeneousLocalization.algebraMap_apply, overPow_val_mul_pow] at hu'
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔮) 𝔮 _).mp hu' had

/-- **Lengths over the homogeneous and the ordinary localization agree.** Let `A` be an
`ℕ`-graded domain, `𝔮` a homogeneous prime and `f ∈ A₁ ∖ 𝔮`. For every ideal `I` of the
homogeneous localization `A₍𝔮₎`, `ℓ_{A_𝔮}(A_𝔮 / I A_𝔮) = ℓ_{A₍𝔮₎}(A₍𝔮₎ / I)`. -/
theorem length_quotient_map_atPrime (h𝔮 : 𝔮.IsHomogeneous 𝒜) {f : A} (hf : f ∈ 𝒜 1)
    (hf𝔮 : f ∉ 𝔮) (I : Ideal (HomogeneousLocalization.AtPrime 𝒜 𝔮)) :
    Module.length (Localization.AtPrime 𝔮)
        (Localization.AtPrime 𝔮 ⧸ I.map (algebraMap _ (Localization.AtPrime 𝔮))) =
      Module.length (HomogeneousLocalization.AtPrime 𝒜 𝔮)
        (HomogeneousLocalization.AtPrime 𝒜 𝔮 ⧸ I) := by
  have := flat_atPrime 𝒜 𝔮 hf hf𝔮
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime 𝔮)
    I).toLinearEquiv.length_eq, IsLocalRing.length_baseChange,
    map_maximalIdeal_atPrime 𝒜 𝔮 h𝔮 hf hf𝔮]
  rw [Module.length_eq_one_iff.mpr (isSimpleModule_iff_isCoatom.mpr
    (maximalIdeal.isMaximal (Localization.AtPrime 𝔮)).out), mul_one]

end Hartshorne.GradedLocalizationLength
