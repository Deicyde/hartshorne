/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.Algebra.GradedMulAction
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Degree-zero localization of a graded module

Hartshorne, *Algebraic Geometry*, II.5, the definition of `M_(𝔭)` and `M_(f)` before
Proposition 5.11 (p. 116).

Let `S` be an `ℕ`-graded ring, `M` a `ℤ`-graded `S`-module and `T` a multiplicative subset
of `S`. Hartshorne's degree-zero localization `M_(T)` consists of the fractions `m / s` in
`T⁻¹ M` with `m` and `s` homogeneous of the same degree. It is a module over the
degree-zero localization `S_(T)` of the ring, which Mathlib calls `HomogeneousLocalization`.

Mathlib has `HomogeneousLocalization` only for the ring itself. This file builds the module
version as a submodule of `LocalizedModule T M`, with scalars restricted along the inclusion
`S_(T) → T⁻¹ S`.

The module grading is indexed by `ℤ`, as in Hartshorne, so that twists `M(n)` make sense;
`ℕ` acts on `ℤ` by translation to state that the action of `S` is graded.

## Main definitions

* `Hartshorne.instVAddNatInt`: translation of `ℤ`-degrees by `ℕ`-degrees.
* `Hartshorne.homogeneousLocalizedSubmodule`: the degree-zero fractions inside `T⁻¹ M`.
* `Hartshorne.HomogeneousLocalizedModule`: Hartshorne's `M_(T)`, an `S_(T)`-module.
* `Hartshorne.HomogeneousLocalizedModule.mk`: the fraction `m / s`.
-/

namespace Hartshorne

/-- `ℕ`-degrees translate `ℤ`-degrees: `n +ᵥ i = n + i`. This lets an `ℕ`-graded ring act
gradedly on a `ℤ`-graded module through `SetLike.GradedSMul`. -/
scoped instance instVAddNatInt : VAdd ℕ ℤ := ⟨fun n i => (n : ℤ) + i⟩

theorem natVAddInt_def (n : ℕ) (i : ℤ) : n +ᵥ i = (n : ℤ) + i := rfl

open HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {M σM : Type*} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
  (ℳ : ℤ → σM) [SetLike.GradedSMul 𝒜 ℳ]
  (x : Submonoid A)

/-- `LocalizedModule x M` as a module over the degree-zero localization `S_(x)`, by restricting
scalars along `S_(x) → x⁻¹ S`. Only used locally to cut out the degree-zero submodule. -/
noncomputable abbrev localizedModuleHomogeneousModule :
    Module (HomogeneousLocalization 𝒜 x) (LocalizedModule x M) :=
  Module.compHom _ (algebraMap (HomogeneousLocalization 𝒜 x) (Localization x))

attribute [local instance] localizedModuleHomogeneousModule

omit [SetLike.GradedSMul 𝒜 ℳ] in
theorem localizedModuleHomogeneous_smul_def (c : HomogeneousLocalization 𝒜 x)
    (y : LocalizedModule x M) : c • y = c.val • y := rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [AddSubgroupClass σM M] in
/-- The graded action in the form used below: `S_n • M_i ⊆ M_(n + i)`. -/
theorem smul_mem_graded_nat {n : ℕ} {i : ℤ} {a : A} {m : M} (ha : a ∈ 𝒜 n) (hm : m ∈ ℳ i) :
    a • m ∈ ℳ ((n : ℤ) + i) :=
  SetLike.GradedSMul.smul_mem ha hm

/-- The degree-zero fractions `m / s` in `x⁻¹ M`: `m ∈ M_n` and `s ∈ S_n ∩ x` for some `n`. -/
noncomputable def homogeneousLocalizedSubmodule :
    Submodule (HomogeneousLocalization 𝒜 x) (LocalizedModule x M) where
  carrier := {y | ∃ (n : ℕ) (m : M) (s : A) (_ : m ∈ ℳ n) (_ : s ∈ 𝒜 n) (hs : s ∈ x),
    y = LocalizedModule.mk m ⟨s, hs⟩}
  zero_mem' := ⟨0, 0, 1, zero_mem _, SetLike.GradedOne.one_mem, one_mem _,
    (LocalizedModule.zero_mk _).symm⟩
  add_mem' := by
    rintro _ _ ⟨n, m, s, hm, hs, hsx, rfl⟩ ⟨n', m', s', hm', hs', hsx', rfl⟩
    refine ⟨n + n', s' • m + s • m', s * s', add_mem ?_ ?_,
      SetLike.GradedMul.mul_mem hs hs', mul_mem hsx hsx', ?_⟩
    · have := smul_mem_graded_nat 𝒜 ℳ hs' hm
      rwa [show ((n' : ℕ) : ℤ) + n = ((n + n' : ℕ) : ℤ) by push_cast; ring] at this
    · have := smul_mem_graded_nat 𝒜 ℳ hs hm'
      rwa [show ((n : ℕ) : ℤ) + n' = ((n + n' : ℕ) : ℤ) by push_cast; ring] at this
    · rw [LocalizedModule.mk_add_mk]
      rfl
  smul_mem' := by
    rintro c _ ⟨n, m, s, hm, hs, hsx, rfl⟩
    obtain ⟨⟨i, ⟨a, ha⟩, ⟨b, hb⟩, hbx⟩, rfl⟩ := HomogeneousLocalization.mk_surjective c
    refine ⟨i + n, a • m, b * s, ?_, SetLike.GradedMul.mul_mem hb hs, mul_mem hbx hsx, ?_⟩
    · have := smul_mem_graded_nat 𝒜 ℳ ha hm
      rwa [show ((i : ℕ) : ℤ) + n = ((i + n : ℕ) : ℤ) by push_cast; ring] at this
    · rw [localizedModuleHomogeneous_smul_def, HomogeneousLocalization.val_mk]
      exact LocalizedModule.mk_smul_mk _ _ _ _

/-- Hartshorne's `M_(x)`: the degree-zero part of the localization of the graded module `M`
at the multiplicative set `x`, as a module over the degree-zero localization `S_(x)`. -/
abbrev HomogeneousLocalizedModule : Type _ := homogeneousLocalizedSubmodule 𝒜 ℳ x

namespace HomogeneousLocalizedModule

noncomputable instance : Module (HomogeneousLocalization 𝒜 x)
    (HomogeneousLocalizedModule 𝒜 ℳ x) :=
  Submodule.module _

variable {𝒜 ℳ x}

/-- The fraction `m / s` with `m ∈ M_n`, `s ∈ S_n` and `s ∈ x`. -/
noncomputable def mk (n : ℕ) (m : M) (hm : m ∈ ℳ n) (s : A) (hs : s ∈ 𝒜 n) (hsx : s ∈ x) :
    HomogeneousLocalizedModule 𝒜 ℳ x :=
  ⟨LocalizedModule.mk m ⟨s, hsx⟩, n, m, s, hm, hs, hsx, rfl⟩

/-- The underlying element of `x⁻¹ M`. -/
def val (y : HomogeneousLocalizedModule 𝒜 ℳ x) : LocalizedModule x M := y.1

theorem val_injective :
    Function.Injective (val : HomogeneousLocalizedModule 𝒜 ℳ x → LocalizedModule x M) :=
  Subtype.val_injective

@[ext]
theorem ext {y z : HomogeneousLocalizedModule 𝒜 ℳ x} (h : y.val = z.val) : y = z :=
  val_injective h

@[simp]
theorem val_mk (n : ℕ) (m : M) (hm : m ∈ ℳ n) (s : A) (hs : s ∈ 𝒜 n) (hsx : s ∈ x) :
    (mk n m hm s hs hsx).val = LocalizedModule.mk m ⟨s, hsx⟩ := rfl

theorem mk_surjective (y : HomogeneousLocalizedModule 𝒜 ℳ x) :
    ∃ (n : ℕ) (m : M) (hm : m ∈ ℳ n) (s : A) (hs : s ∈ 𝒜 n) (hsx : s ∈ x),
      y = mk n m hm s hs hsx := by
  obtain ⟨_, n, m, s, hm, hs, hsx, rfl⟩ := y
  exact ⟨n, m, hm, s, hs, hsx, rfl⟩

@[simp] theorem val_zero : (0 : HomogeneousLocalizedModule 𝒜 ℳ x).val = 0 := rfl

@[simp] theorem val_add (y z : HomogeneousLocalizedModule 𝒜 ℳ x) :
    (y + z).val = y.val + z.val := rfl

@[simp] theorem val_neg (y : HomogeneousLocalizedModule 𝒜 ℳ x) : (-y).val = -y.val := rfl

@[simp] theorem val_sub (y z : HomogeneousLocalizedModule 𝒜 ℳ x) :
    (y - z).val = y.val - z.val := rfl

@[simp] theorem val_smul (c : HomogeneousLocalization 𝒜 x)
    (y : HomogeneousLocalizedModule 𝒜 ℳ x) : (c • y).val = c.val • y.val := rfl

end HomogeneousLocalizedModule

end Hartshorne
