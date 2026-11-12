/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# A prime of `B[t]` cut out by a minimal polynomial

Let `S` be a domain, `P` a prime of `S[t]` containing a monic polynomial, `P' = P ∩ S`,
`R = S / P'`, and `B` the integral closure of `R` in its fraction field `K`. The image `t̄` of `t`
in the fraction field `L` of `S[t] / P` is integral over `R`, hence over `B`; let `g` be its
minimal polynomial over `B`. Since `B` is integrally closed, the polynomials over `B` vanishing at
`t̄` are exactly the multiples of `g` (`minpoly.isIntegrallyClosed_dvd_iff`), so `(g)` is the
kernel of `B[t] → L`, a prime ideal, and its contraction to `S[t]` (along
`S[t] → R[t] → B[t]`) is `P` (`exists_minpoly_span_isPrime_comap_eq`).

Moreover `B[t]` is integral over `R[t]`, and every element of `B[t]` times a nonzero constant
of `R` lies in `R[t]` (`exists_C_mul_eq_map_integralClosure`).
-/

namespace Hartshorne

open Polynomial

section IntegralClosure

variable (R : Type*) [CommRing R] [IsDomain R]

/-- The integral closure of a domain in its fraction field is integrally closed. -/
instance isIntegrallyClosed_integralClosure_fractionRing :
    IsIntegrallyClosed (integralClosure R (FractionRing R)) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)

variable {R}

/-- Every polynomial over the integral closure `B` of `R` in its fraction field becomes a
polynomial over `R` after multiplication by a nonzero constant of `R`. -/
theorem exists_C_mul_eq_map_integralClosure (a : (integralClosure R (FractionRing R))[X]) :
    ∃ b : R, b ≠ 0 ∧ ∃ d : R[X],
      C (algebraMap R (integralClosure R (FractionRing R)) b) * a =
        d.map (algebraMap R (integralClosure R (FractionRing R))) := by
  classical
  let K := FractionRing R
  let B := integralClosure R K
  obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R)
    (a.map (algebraMap B K))
  refine ⟨b, nonZeroDivisors.ne_zero hb,
    IsLocalization.integerNormalization (nonZeroDivisors R) (a.map (algebraMap B K)), ?_⟩
  apply Polynomial.map_injective (algebraMap B K) Subtype.val_injective
  rw [Polynomial.map_mul, map_C, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, hbp,
    Algebra.smul_def, Polynomial.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

omit [IsDomain R] in
/-- `B[t]` is integral over `R[t]`. -/
theorem isIntegral_mapRingHom_integralClosure :
    @RingHom.IsIntegral R[X] (integralClosure R (FractionRing R))[X] _ _
      (mapRingHom (algebraMap R (integralClosure R (FractionRing R)))) := by
  let _ := Polynomial.algebra (R := R) (A := integralClosure R (FractionRing R))
  exact fun a => Algebra.IsIntegral.isIntegral (R := R[X]) a

theorem injective_mapRingHom_integralClosure :
    Function.Injective (mapRingHom (algebraMap R (integralClosure R (FractionRing R)))) :=
  Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective R _)

end IntegralClosure

section MinimalPolynomial

variable {S : Type*} [CommRing S]

/-- **The prime cut out by the minimal polynomial.** Let `P` be a prime of `S[t]` containing a
monic polynomial, `P' = P ∩ S`, `R = S / P'`, and `B` the integral closure of `R` in its fraction
field. There is a nonzero `g ∈ B[t]` such that `(g)` is prime and its contraction to `S[t]` along
`S[t] → R[t] → B[t]` is `P`. -/
theorem exists_minpoly_span_isPrime_comap_eq (P : Ideal S[X]) [P.IsPrime] {h : S[X]}
    (hmon : h.Monic) (hP : h ∈ P) :
    ∃ g : (integralClosure (S ⧸ P.comap C) (FractionRing (S ⧸ P.comap C)))[X], g ≠ 0 ∧
      (Ideal.span {g}).IsPrime ∧
      (Ideal.span {g}).comap
        ((mapRingHom (algebraMap (S ⧸ P.comap C)
          (integralClosure (S ⧸ P.comap C) (FractionRing (S ⧸ P.comap C))))).comp
          (mapRingHom (Ideal.Quotient.mk (P.comap C)))) = P := by
  classical
  set P' := P.comap (C : S →+* S[X])
  let R := S ⧸ P'
  let K := FractionRing R
  let B := integralClosure R K
  let L := FractionRing (S[X] ⧸ P)
  -- `R → S[t] / P → L` is injective
  let ρ₀ : R →+* S[X] ⧸ P := Ideal.quotientMap P C le_rfl
  have hρ₀ : Function.Injective ρ₀ := Ideal.quotientMap_injective
  let ρ : R →+* L := (algebraMap (S[X] ⧸ P) L).comp ρ₀
  have hρ : Function.Injective ρ := fun x y hxy => hρ₀ (IsFractionRing.injective _ L hxy)
  let κ : K →+* L := IsFractionRing.lift hρ
  let ι : B →+* L := κ.comp (algebraMap B K)
  have hι : Function.Injective ι := κ.injective.comp Subtype.val_injective
  let tbar : L := algebraMap (S[X] ⧸ P) L (Ideal.Quotient.mk P X)
  -- the map `S[t] → R[t] → B[t] → L` is `S[t] → S[t] / P → L`
  have hκ : ∀ r : R, κ (algebraMap R K r) = ρ r := fun r => IsFractionRing.lift_algebraMap hρ r
  have hcomp : ((eval₂RingHom ι tbar).comp ((mapRingHom (algebraMap R B)).comp
      (mapRingHom (Ideal.Quotient.mk P')))) =
      (algebraMap (S[X] ⧸ P) L).comp (Ideal.Quotient.mk P) := by
    apply Polynomial.ringHom_ext
    · intro s
      simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C,
        coe_eval₂RingHom, eval₂_C]
      change κ (algebraMap B K (algebraMap R B (Ideal.Quotient.mk P' s))) = _
      rw [← IsScalarTower.algebraMap_apply, hκ]
      rfl
    · simp [tbar]
  let _ : Algebra B L := ι.toAlgebra
  have hint : IsIntegral B tbar := by
    refine ⟨(h.map (Ideal.Quotient.mk P')).map (algebraMap R B), (hmon.map _).map _, ?_⟩
    change eval₂ ι tbar _ = 0
    have := congrArg (fun φ => φ h) hcomp
    simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coe_eval₂RingHom] at this
    rw [this, Ideal.Quotient.eq_zero_iff_mem.mpr hP, map_zero]
  have : Module.IsTorsionFree B L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hι
  set g := minpoly B tbar
  have hker : ∀ f : B[X], f ∈ Ideal.span {g} ↔ eval₂RingHom ι tbar f = 0 := by
    intro f
    rw [Ideal.mem_span_singleton, ← minpoly.isIntegrallyClosed_dvd_iff hint f, aeval_def]
    rfl
  have hspan : Ideal.span {g} = RingHom.ker (eval₂RingHom ι tbar) := by
    ext f
    rw [hker, RingHom.mem_ker]
  refine ⟨g, minpoly.ne_zero hint, ?_, ?_⟩
  · rw [hspan]
    exact RingHom.ker_isPrime _
  · ext f
    rw [Ideal.mem_comap, hker, ← RingHom.comp_apply, hcomp,
      RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ L),
      Ideal.Quotient.eq_zero_iff_mem]

end MinimalPolynomial

end Hartshorne
