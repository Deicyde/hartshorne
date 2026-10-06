/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Exact.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The complex exponential exact sequence

Hartshorne, *Algebraic Geometry*, Appendix B, §5 (p. 446).

The normalized exponential `z ↦ exp (2 · π · i · z)` gives the short exact
sequence of abelian groups

`0 → ℤ → ℂ → ℂˣ → 0`.

We regard the unit group multiplicatively and then apply the `Additive` type
tag so that all three displayed arrows are additive homomorphisms.
-/

namespace Hartshorne

open Complex
open scoped Real

/-- The inclusion of the integers into the additive group of complex numbers. -/
def integerToComplex : ℤ →+ ℂ :=
  Int.castAddHom ℂ

/-- The normalized complex exponential, valued in the additive avatar of the
unit group `ℂˣ`. -/
noncomputable def normalizedComplexExponential : ℂ →+ Additive ℂˣ where
  toFun z := Additive.ofMul (Units.mk0 (Complex.exp (z * (2 * π * I))) (Complex.exp_ne_zero _))
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    simp
  map_add' z w := by
    apply Additive.toMul.injective
    apply Units.ext
    change Complex.exp ((z + w) * (2 * π * I)) =
      Complex.exp (z * (2 * π * I)) * Complex.exp (w * (2 * π * I))
    rw [add_mul, Complex.exp_add]

/-- The normalized complex exponential realizes the short exact sequence
`0 → ℤ → ℂ → ℂˣ → 0`.

Injectivity and surjectivity encode exactness at the two ends, while
`Function.Exact` says that the kernel of the exponential consists precisely
of the embedded integers. -/
theorem complexExponentialExactSequence :
    Function.Injective integerToComplex ∧
      Function.Exact integerToComplex normalizedComplexExponential ∧
      Function.Surjective normalizedComplexExponential := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n h
    exact Int.cast_injective h
  · intro z
    constructor
    · intro hz
      have hz' : Complex.exp (z * (2 * π * I)) = 1 := by
        simpa [normalizedComplexExponential] using
          congrArg (fun v : Additive ℂˣ ↦ (v.toMul : ℂ)) hz
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hz'
      have hfactor : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      have hzcast : z = (n : ℂ) := by
        exact mul_right_cancel₀ hfactor hn
      exact ⟨n, hzcast.symm⟩
    · rintro ⟨n, rfl⟩
      apply Additive.toMul.injective
      apply Units.ext
      change Complex.exp ((n : ℂ) * (2 * π * I)) = 1
      exact Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩
  · intro u
    let c : ℂ := (u.toMul : ℂ)
    have hc : c ≠ 0 := Units.ne_zero u.toMul
    refine ⟨Complex.log c / (2 * π * I), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    change Complex.exp ((Complex.log c / (2 * π * I)) * (2 * π * I)) = c
    rw [div_mul_cancel₀ _ Complex.two_pi_I_ne_zero, Complex.exp_log hc]

end Hartshorne
