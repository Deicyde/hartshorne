/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.PrincipalDivisor

/-!
# Linear equivalence and the Weil divisor class group

Hartshorne, *Algebraic Geometry*, II.6, p. 131.
-/

noncomputable section

namespace AlgebraicGeometry

universe u

/-- The subgroup of principal Weil divisors. -/
noncomputable def Scheme.principalDivisorSubgroup
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    AddSubgroup X.WeilDivisor := by
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  exact (X.principalDivisorHom hX).range

/-- Two Weil divisors are linearly equivalent when their difference is
principal. -/
noncomputable def Scheme.WeilDivisor.LinearEquivalent
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar)
    (D E : X.WeilDivisor) : Prop :=
  D - E ∈ X.principalDivisorSubgroup hX

/-- The Weil divisor class group. -/
noncomputable abbrev Scheme.WeilClassGroup
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :=
  X.WeilDivisor ⧸ X.principalDivisorSubgroup hX

/-- The canonical homomorphism from Weil divisors to their divisor classes. -/
noncomputable def Scheme.weilDivisorClassHom
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    X.WeilDivisor →+ X.WeilClassGroup hX :=
  QuotientAddGroup.mk' (X.principalDivisorSubgroup hX)

/-- Linear equivalence means that the oriented difference `D - E` is the
principal divisor of a nonzero rational function. -/
theorem Scheme.WeilDivisor.linearEquivalent_iff
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar)
    (D E : X.WeilDivisor) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    LinearEquivalent hX D E ↔
      ∃ f : X.functionFieldˣ, D - E = X.principalDivisor hX f := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  constructor
  · intro h
    change D - E ∈ (X.principalDivisorHom hX).range at h
    obtain ⟨f, hf⟩ := AddMonoidHom.mem_range.mp h
    exact ⟨f.toMul, hf.symm⟩
  · rintro ⟨f, hf⟩
    change D - E ∈ (X.principalDivisorHom hX).range
    apply AddMonoidHom.mem_range.mpr
    exact ⟨Additive.ofMul f, hf.symm⟩

/-- Two Weil divisors have the same class if and only if their oriented
difference is principal. -/
theorem Scheme.weilDivisorClass_eq_iff
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar)
    (D E : X.WeilDivisor) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    X.weilDivisorClassHom hX D = X.weilDivisorClassHom hX E ↔
      ∃ f : X.functionFieldˣ, D - E = X.principalDivisor hX f := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  change ((D : X.WeilClassGroup hX) = E) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact Scheme.WeilDivisor.linearEquivalent_iff hX D E

end AlgebraicGeometry
