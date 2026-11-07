/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.HomogeneousLocalizedModule

/-!
# The twisted graded modules `S(n)`

Hartshorne, *Algebraic Geometry*, II.5, the definition of the twisted module `M(n)` before
Proposition 5.12 (p. 117), for `M = S`.

Let `S` be an `ℕ`-graded ring and `n ∈ ℤ`. The twisted module `S(n)` is `S` itself, regraded by
`ℤ` with `S(n)_d = S_{n+d}`; here `S_k = 0` for `k < 0`. It is a graded `S`-module, since
`S_i · S(n)_d = S_i · S_{n+d} ⊆ S_{n+i+d} = S(n)_{i+d}`, and its homogeneous components form a
direct sum decomposition of `S`.

## Main definitions

* `Hartshorne.gradedTwist 𝒜 n`: the grading `d ↦ S(n)_d = S_{n+d}` of `S` by `ℤ`.
* `Hartshorne.gradedTwist.gradedSMul`: `S(n)` is a graded `S`-module.
* `Hartshorne.gradedTwist.decomposition`: `S` is the direct sum of the `S(n)_d`.
-/

namespace Hartshorne

open DirectSum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)

/-- Hartshorne's twist `S(n)` of a graded ring `S`, as a `ℤ`-grading of `S`: the degree `d`
component is `S(n)_d = S_{n+d}`, which is `0` when `n + d < 0`. -/
def gradedTwist (n d : ℤ) : AddSubgroup A where
  carrier := {a | a ∈ 𝒜 (n + d).toNat ∧ (n + d < 0 → a = 0)}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, fun h => by rw [ha.2 h, hb.2 h, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun _ => rfl⟩
  neg_mem' ha := ⟨neg_mem ha.1, fun h => by rw [ha.2 h, neg_zero]⟩

variable {𝒜}

/-- `S(n)_d = S_k` when `n + d = k`. -/
theorem mem_gradedTwist_of_eq {n d : ℤ} {k : ℕ} (h : n + d = k) {a : A} :
    a ∈ gradedTwist 𝒜 n d ↔ a ∈ 𝒜 k := by
  change a ∈ 𝒜 (n + d).toNat ∧ (n + d < 0 → a = 0) ↔ _
  rw [h, Int.toNat_natCast]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', fun h'' => absurd h'' (by omega)⟩⟩

theorem mem_of_mem_gradedTwist {n d : ℤ} {a : A} (ha : a ∈ gradedTwist 𝒜 n d) :
    a ∈ 𝒜 (n + d).toNat :=
  ha.1

theorem eq_zero_of_mem_gradedTwist {n d : ℤ} {a : A} (ha : a ∈ gradedTwist 𝒜 n d)
    (h : n + d < 0) : a = 0 :=
  ha.2 h

variable [GradedRing 𝒜]

/-- **`S(n)` is a graded `S`-module**: `S_i · S(n)_d ⊆ S(n)_{i+d}`. -/
instance gradedTwist.gradedSMul (n : ℤ) : SetLike.GradedSMul 𝒜 (gradedTwist 𝒜 n) where
  smul_mem := by
    intro i d a b ha hb
    rw [natVAddInt_def]
    by_cases h : n + d < 0
    · rw [eq_zero_of_mem_gradedTwist hb h, smul_zero]
      exact zero_mem _
    · refine (mem_gradedTwist_of_eq (k := i + (n + d).toNat) (by omega)).2 ?_
      exact SetLike.GradedMul.mul_mem ha (mem_of_mem_gradedTwist hb)

/-- The inclusion `S_k → S(n)_{k-n}`. -/
def gradedTwistIncl (n : ℤ) (k : ℕ) : 𝒜 k →+ gradedTwist 𝒜 n ((k : ℤ) - n) where
  toFun x := ⟨x, (mem_gradedTwist_of_eq (by omega)).2 x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (𝒜) in
/-- The decomposition of `S` into the components `S(n)_d`: the component of `a` in `S(n)_d` is
its component in `S_{n+d}`. -/
noncomputable def gradedTwistDecompose (n : ℤ) : A →+ ⨁ d : ℤ, gradedTwist 𝒜 n d :=
  (DirectSum.toAddMonoid fun k : ℕ =>
    (DirectSum.of (fun d : ℤ => gradedTwist 𝒜 n d) ((k : ℤ) - n)).comp (gradedTwistIncl n k)).comp
    (decomposeAddEquiv 𝒜).toAddMonoidHom

theorem gradedTwistDecompose_of_mem (n : ℤ) {k : ℕ} {a : A} (ha : a ∈ 𝒜 k) :
    gradedTwistDecompose 𝒜 n a =
      DirectSum.of (fun d : ℤ => gradedTwist 𝒜 n d) ((k : ℤ) - n)
        ⟨a, (mem_gradedTwist_of_eq (by omega)).2 ha⟩ := by
  classical
  simp only [gradedTwistDecompose, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, decomposeAddEquiv_apply, decompose_of_mem 𝒜 ha,
    DirectSum.toAddMonoid_of]
  rfl

/-- **The homogeneous components of `S(n)` decompose `S`.** -/
noncomputable instance gradedTwist.decomposition (n : ℤ) :
    DirectSum.Decomposition (gradedTwist 𝒜 n) :=
  .ofAddHom (gradedTwist 𝒜 n) (gradedTwistDecompose 𝒜 n)
    (by
      ext a
      induction a using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | @homogeneous k a =>
        obtain ⟨a, ha⟩ := a
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply,
          gradedTwistDecompose_of_mem n ha, DirectSum.coeAddMonoidHom_of]
      | add a b ha hb =>
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply,
          map_add] at ha hb ⊢
        rw [ha, hb])
    (by
      refine DirectSum.addHom_ext fun d y => ?_
      obtain ⟨y, hy⟩ := y
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      by_cases h : n + d < 0
      · obtain rfl := eq_zero_of_mem_gradedTwist hy h
        rw [map_zero]
        exact (map_zero (DirectSum.of (fun d : ℤ => gradedTwist 𝒜 n d) d)).symm
      · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 h)
        obtain rfl : d = (k : ℤ) - n := by omega
        rw [gradedTwistDecompose_of_mem n ((mem_gradedTwist_of_eq hk).1 hy)])

end Hartshorne
