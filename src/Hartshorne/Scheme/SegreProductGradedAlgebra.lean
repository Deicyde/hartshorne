/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The diagonal (Segre) product of two graded algebras

Supplements Hartshorne, *Algebraic Geometry*, II.7, Lemma 7.9 (p. 161). Let `A` be a commutative
ring and `S = ⊕_d S_d`, `T = ⊕_d T_d` two `ℕ`-graded commutative `A`-algebras on which `A` acts in
degree zero. The *diagonal product* of `S` and `T` is the subalgebra
`S ×_A T = ⊕_d S_d ⊗_A T_d` of `S ⊗_A T`, graded by `(S ×_A T)_d = S_d ⊗_A T_d` (more precisely,
by the image of `S_d ⊗_A T_d` in `S ⊗_A T`). For `T = ⊕_d L^{⊗ d}` with `L` an invertible
`A`-module it is the graded algebra `S · L` of Lemma 7.9.

## Main definitions and results

* `Hartshorne.SegreProduct.component`: the image of `S_d ⊗_A T_d` in `S ⊗_A T`.
* `Hartshorne.SegreProduct.diagonal`: the subalgebra `⊕_d S_d ⊗_A T_d`.
* `Hartshorne.SegreProduct.grading`: its grading, a `GradedRing`; the degree-`d` component of
  `x` is `(p_d ⊗ q_d)(x)` where `p_d`, `q_d` are the projections to degree `d`
  (`Hartshorne.SegreProduct.coe_decompose`).
* `Hartshorne.SegreProduct.diagonalMap`: the graded ring map induced by compatible graded ring
  maps `S → S'`, `T → T'` over `A → A'`; it is functorial (`diagonalMap_id`,
  `diagonalMap_comp`).
* `Hartshorne.SegreProduct.isLocalizationAway_diagonalMap`: if `A' = A[1/r]`, `S' = S[1/r]`
  and `T' = T[1/r]`, then `S' ×_{A'} T' = (S ×_A T)[1/r]`.
-/

noncomputable section

open TensorProduct DirectSum

namespace Hartshorne

namespace SegreProduct

variable {A S T : Type*} [CommRing A] [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
  (𝒮 : ℕ → AddSubgroup S) (𝒯 : ℕ → AddSubgroup T) [GradedRing 𝒮] [GradedRing 𝒯]

variable (A) in
/-- The image of `S_d ⊗_A T_d` in `S ⊗_A T`: the span of the pure tensors `s ⊗ t` with `s`, `t`
homogeneous of degree `d`. -/
def component (d : ℕ) : Submodule A (S ⊗[A] T) :=
  Submodule.span A {x | ∃ s ∈ 𝒮 d, ∃ t ∈ 𝒯 d, s ⊗ₜ t = x}

omit [GradedRing 𝒮] [GradedRing 𝒯] in
variable {𝒮 𝒯} in
theorem tmul_mem_component {d : ℕ} {s : S} (hs : s ∈ 𝒮 d) {t : T} (ht : t ∈ 𝒯 d) :
    s ⊗ₜ[A] t ∈ component A 𝒮 𝒯 d :=
  Submodule.subset_span ⟨s, hs, t, ht, rfl⟩

variable {𝒮 𝒯} in
theorem mul_mem_component {i j : ℕ} {x y : S ⊗[A] T} (hx : x ∈ component A 𝒮 𝒯 i)
    (hy : y ∈ component A 𝒮 𝒯 j) : x * y ∈ component A 𝒮 𝒯 (i + j) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s', hs', t', ht', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_component (SetLike.mul_mem_graded hs hs') (SetLike.mul_mem_graded ht ht')
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

theorem one_mem_component : (1 : S ⊗[A] T) ∈ component A 𝒮 𝒯 0 :=
  tmul_mem_component (SetLike.one_mem_graded 𝒮) (SetLike.one_mem_graded 𝒯)

variable (A) in
/-- The diagonal product `S ×_A T = ⊕_d S_d ⊗_A T_d`, a subalgebra of `S ⊗_A T`. -/
def diagonal : Subalgebra A (S ⊗[A] T) :=
  (⨆ d, component A 𝒮 𝒯 d).toSubalgebra
    (Submodule.mem_iSup_of_mem 0 (one_mem_component 𝒮 𝒯))
    (fun x y hx hy => by
      refine Submodule.iSup_induction _ (motive := fun x => x * y ∈ ⨆ d, component A 𝒮 𝒯 d) hx
        (fun i x hx => ?_) (by simp) (fun x z hx hz => by rw [add_mul]; exact add_mem hx hz)
      refine Submodule.iSup_induction _ (motive := fun y => x * y ∈ ⨆ d, component A 𝒮 𝒯 d) hy
        (fun j y hy => ?_) (by simp) (fun y z hy hz => by rw [mul_add]; exact add_mem hy hz)
      exact Submodule.mem_iSup_of_mem (i + j) (mul_mem_component hx hy))

variable {𝒮 𝒯} in
theorem mem_diagonal_iff {x : S ⊗[A] T} : x ∈ diagonal A 𝒮 𝒯 ↔ x ∈ ⨆ d, component A 𝒮 𝒯 d :=
  Iff.rfl

variable {𝒮 𝒯} in
theorem mem_diagonal_of_mem {d : ℕ} {x : S ⊗[A] T} (hx : x ∈ component A 𝒮 𝒯 d) :
    x ∈ diagonal A 𝒮 𝒯 :=
  Submodule.mem_iSup_of_mem d hx

variable (A) in
/-- The grading `(S ×_A T)_d = S_d ⊗_A T_d` of the diagonal product. -/
def grading (d : ℕ) : AddSubgroup (diagonal A 𝒮 𝒯) :=
  (component A 𝒮 𝒯 d).toAddSubgroup.comap (diagonal A 𝒮 𝒯).val.toRingHom.toAddMonoidHom

variable {𝒮 𝒯} in
theorem mem_grading_iff {d : ℕ} {x : diagonal A 𝒮 𝒯} :
    x ∈ grading A 𝒮 𝒯 d ↔ (x : S ⊗[A] T) ∈ component A 𝒮 𝒯 d :=
  AddSubgroup.mem_comap

instance gradedMonoid : SetLike.GradedMonoid (grading A 𝒮 𝒯) where
  one_mem := mem_grading_iff.2 (one_mem_component 𝒮 𝒯)
  mul_mem _ _ _ _ hx hy := mem_grading_iff.2 (mul_mem_component (mem_grading_iff.1 hx)
    (mem_grading_iff.1 hy))

/-! ### Projections to the homogeneous components -/

section Proj

variable (h𝒮 : ∀ a : A, algebraMap A S a ∈ 𝒮 0) (h𝒯 : ∀ a : A, algebraMap A T a ∈ 𝒯 0)

/-- The projection of a graded `A`-algebra (with `A` acting in degree zero) to its degree-`d`
part, as an `A`-linear map. -/
def projLinear {R : Type*} [CommRing R] [Algebra A R] (ℛ : ℕ → AddSubgroup R) [GradedRing ℛ]
    (hℛ : ∀ a : A, algebraMap A R a ∈ ℛ 0) (d : ℕ) : R →ₗ[A] R where
  toFun x := decompose ℛ x d
  map_add' x y := by simp
  map_smul' a x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    exact coe_decompose_mul_of_left_mem_zero ℛ (hℛ a)

/-- The projection `p_d ⊗ q_d : S ⊗_A T → S_d ⊗_A T_d ⊆ S ⊗_A T`. -/
def tproj (d : ℕ) : S ⊗[A] T →ₗ[A] S ⊗[A] T :=
  TensorProduct.map (projLinear 𝒮 h𝒮 d) (projLinear 𝒯 h𝒯 d)

@[simp]
theorem tproj_tmul (d : ℕ) (s : S) (t : T) :
    tproj 𝒮 𝒯 h𝒮 h𝒯 d (s ⊗ₜ t) = (decompose 𝒮 s d : S) ⊗ₜ (decompose 𝒯 t d : T) :=
  rfl

theorem tproj_mem (d : ℕ) (x : S ⊗[A] T) : tproj 𝒮 𝒯 h𝒮 h𝒯 d x ∈ component A 𝒮 𝒯 d := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s t => exact tmul_mem_component (decompose 𝒮 s d).2 (decompose 𝒯 t d).2
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem tproj_of_mem_same {d : ℕ} {y : S ⊗[A] T} (hy : y ∈ component A 𝒮 𝒯 d) :
    tproj 𝒮 𝒯 h𝒮 h𝒯 d y = y := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hx
    rw [tproj_tmul, decompose_of_mem_same 𝒮 hs, decompose_of_mem_same 𝒯 ht]
  | zero => simp
  | add x z _ _ hx hz => rw [map_add, hx, hz]
  | smul a x _ hx => rw [map_smul, hx]

theorem tproj_of_mem_ne {d e : ℕ} (hde : e ≠ d) {y : S ⊗[A] T} (hy : y ∈ component A 𝒮 𝒯 e) :
    tproj 𝒮 𝒯 h𝒮 h𝒯 d y = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hx
    rw [tproj_tmul, decompose_of_mem_ne 𝒮 hs hde, zero_tmul]
  | zero => simp
  | add x z _ _ hx hz => rw [map_add, hx, hz, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

theorem tproj_coeAddMonoidHom (y : ⨁ n, grading A 𝒮 𝒯 n) (n : ℕ) :
    tproj 𝒮 𝒯 h𝒮 h𝒯 n ((DirectSum.coeAddMonoidHom (grading A 𝒮 𝒯) y : diagonal A 𝒮 𝒯) :
      S ⊗[A] T) = ((y n : diagonal A 𝒮 𝒯) : S ⊗[A] T) := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | of m v =>
    rw [coeAddMonoidHom_of]
    by_cases hmn : m = n
    · subst hmn
      rw [of_eq_same]
      exact tproj_of_mem_same 𝒮 𝒯 h𝒮 h𝒯 (mem_grading_iff.1 v.2)
    · rw [of_eq_of_ne _ _ _ (Ne.symm hmn)]
      exact tproj_of_mem_ne 𝒮 𝒯 h𝒮 h𝒯 hmn (mem_grading_iff.1 v.2)
  | add y z hy hz =>
    simp only [map_add, add_apply, AddMemClass.coe_add, hy, hz]

include h𝒮 h𝒯 in
theorem isInternal : DirectSum.IsInternal (grading A 𝒮 𝒯) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    ext n
    have := tproj_coeAddMonoidHom 𝒮 𝒯 h𝒮 h𝒯 y n
    rw [hy] at this
    simpa using this.symm
  · rintro ⟨x, hx⟩
    refine Submodule.iSup_induction' _ (motive := fun x hx =>
        ∃ y : ⨁ n, grading A 𝒮 𝒯 n, DirectSum.coeAddMonoidHom (grading A 𝒮 𝒯) y = ⟨x, hx⟩)
      (fun i x hx => ⟨DirectSum.of _ i ⟨⟨x, mem_diagonal_of_mem hx⟩, mem_grading_iff.2 hx⟩, by simp⟩)
      ⟨0, by simp; rfl⟩ (fun x y hx hy hx' hy' => ?_) hx
    obtain ⟨u, hu⟩ := hx'
    obtain ⟨v, hv⟩ := hy'
    exact ⟨u + v, by rw [map_add, hu, hv]; rfl⟩

end Proj

variable (A) in
/-- The grading of the diagonal product is a graded ring, once `A` acts in degree zero on `S`
and on `T` (a choice of decomposition; see `coe_decompose` for the formula). -/
@[instance_reducible]
def gradedRing (h𝒮 : ∀ a : A, algebraMap A S a ∈ 𝒮 0) (h𝒯 : ∀ a : A, algebraMap A T a ∈ 𝒯 0) :
    GradedRing (grading A 𝒮 𝒯) :=
  { (isInternal 𝒮 𝒯 h𝒮 h𝒯).chooseDecomposition with }


section Decompose

variable (h𝒮 : ∀ a : A, algebraMap A S a ∈ 𝒮 0) (h𝒯 : ∀ a : A, algebraMap A T a ∈ 𝒯 0)

/-- **The homogeneous components of the diagonal product**: the degree-`n` component of `x` is
`(p_n ⊗ q_n)(x)`. -/
theorem coe_decompose (x : diagonal A 𝒮 𝒯) (n : ℕ) :
    letI := gradedRing A 𝒮 𝒯 h𝒮 h𝒯
    ((decompose (grading A 𝒮 𝒯) x n : diagonal A 𝒮 𝒯) : S ⊗[A] T) = tproj 𝒮 𝒯 h𝒮 h𝒯 n x := by
  let := gradedRing A 𝒮 𝒯 h𝒮 h𝒯
  conv_rhs => rw [← (decompose (grading A 𝒮 𝒯)).symm_apply_apply x]
  exact (tproj_coeAddMonoidHom 𝒮 𝒯 h𝒮 h𝒯 _ n).symm

theorem algebraMap_mem_component (a : A) :
    algebraMap A (S ⊗[A] T) a ∈ component A 𝒮 𝒯 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ a (one_mem_component 𝒮 𝒯)

theorem algebraMap_mem_grading (a : A) :
    algebraMap A (diagonal A 𝒮 𝒯) a ∈ grading A 𝒮 𝒯 0 :=
  mem_grading_iff.2 (algebraMap_mem_component 𝒮 𝒯 a)

end Decompose

/-! ### Maps between diagonal products -/

section Map

variable {𝒮 𝒯}

variable {A' S' T' : Type*} [CommRing A'] [CommRing S'] [CommRing T'] [Algebra A' S']
  [Algebra A' T'] {𝒮' : ℕ → AddSubgroup S'} {𝒯' : ℕ → AddSubgroup T'} [GradedRing 𝒮']
  [GradedRing 𝒯'] (α : A →+* A') (σ : 𝒮 →+*ᵍ 𝒮') (τ : 𝒯 →+*ᵍ 𝒯')
  (hσ : ∀ a, σ (algebraMap A S a) = algebraMap A' S' (α a))
  (hτ : ∀ a, τ (algebraMap A T a) = algebraMap A' T' (α a))

/-- The ring map `S ⊗_A T → S' ⊗_{A'} T'`, `s ⊗ t ↦ σ s ⊗ τ t`, induced by ring maps `σ`, `τ`
over `α : A → A'`. -/
def tensorMap : S ⊗[A] T →+* S' ⊗[A'] T' :=
  letI : Algebra A (S' ⊗[A'] T') := ((algebraMap A' (S' ⊗[A'] T')).comp α).toAlgebra
  (Algebra.TensorProduct.lift (R := A) (S := A)
    ({ toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp σ.toRingHom
       commutes' := fun a => by
        change σ (algebraMap A S a) ⊗ₜ 1 = algebraMap A' (S' ⊗[A'] T') (α a)
        rw [hσ, Algebra.TensorProduct.algebraMap_apply] } : S →ₐ[A] S' ⊗[A'] T')
    ({ toRingHom := Algebra.TensorProduct.includeRight.toRingHom.comp τ.toRingHom
       commutes' := fun a => by
        change 1 ⊗ₜ τ (algebraMap A T a) = algebraMap A' (S' ⊗[A'] T') (α a)
        rw [hτ, Algebra.TensorProduct.algebraMap_apply'] } : T →ₐ[A] S' ⊗[A'] T')
    (fun _ _ => Commute.all _ _)).toRingHom

omit [GradedRing 𝒮] [GradedRing 𝒯] [GradedRing 𝒮'] [GradedRing 𝒯'] in
@[simp]
theorem tensorMap_tmul (s : S) (t : T) :
    tensorMap α σ τ hσ hτ (s ⊗ₜ t) = σ s ⊗ₜ τ t := by
  simp [tensorMap, Algebra.TensorProduct.lift_tmul]

omit [GradedRing 𝒮] [GradedRing 𝒯] [GradedRing 𝒮'] [GradedRing 𝒯'] in
theorem tensorMap_algebraMap (a : A) :
    tensorMap α σ τ hσ hτ (algebraMap A (S ⊗[A] T) a) = algebraMap A' (S' ⊗[A'] T') (α a) := by
  rw [Algebra.TensorProduct.algebraMap_apply, tensorMap_tmul, hσ, map_one,
    Algebra.TensorProduct.algebraMap_apply]

omit [GradedRing 𝒮] [GradedRing 𝒯] [GradedRing 𝒮'] [GradedRing 𝒯'] in
theorem tensorMap_mem_component {d : ℕ} {x : S ⊗[A] T} (hx : x ∈ component A 𝒮 𝒯 d) :
    tensorMap α σ τ hσ hτ x ∈ component A' 𝒮' 𝒯' d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hx
    rw [tensorMap_tmul]
    exact tmul_mem_component (σ.map_mem hs) (τ.map_mem ht)
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul, tensorMap_algebraMap, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hx

theorem tensorMap_mem_diagonal {x : S ⊗[A] T} (hx : x ∈ diagonal A 𝒮 𝒯) :
    tensorMap α σ τ hσ hτ x ∈ diagonal A' 𝒮' 𝒯' :=
  Submodule.iSup_induction _ (motive := fun x => tensorMap α σ τ hσ hτ x ∈ diagonal A' 𝒮' 𝒯') hx
    (fun _ _ hx => mem_diagonal_of_mem (tensorMap_mem_component α σ τ hσ hτ hx)) (by simp)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)

/-- The ring map `S ×_A T → S' ×_{A'} T'` of diagonal products induced by graded ring maps `σ`,
`τ` over `α : A → A'`. -/
def diagonalMap : diagonal A 𝒮 𝒯 →+* diagonal A' 𝒮' 𝒯' :=
  (tensorMap α σ τ hσ hτ).restrict (diagonal A 𝒮 𝒯) (diagonal A' 𝒮' 𝒯')
    fun _ hx => tensorMap_mem_diagonal α σ τ hσ hτ hx

@[simp]
theorem coe_diagonalMap (x : diagonal A 𝒮 𝒯) :
    (diagonalMap α σ τ hσ hτ x : S' ⊗[A'] T') = tensorMap α σ τ hσ hτ x :=
  rfl

theorem diagonalMap_mem_grading {d : ℕ} {x : diagonal A 𝒮 𝒯} (hx : x ∈ grading A 𝒮 𝒯 d) :
    diagonalMap α σ τ hσ hτ x ∈ grading A' 𝒮' 𝒯' d :=
  mem_grading_iff.2 (tensorMap_mem_component α σ τ hσ hτ (mem_grading_iff.1 hx))

theorem diagonalMap_algebraMap (a : A) :
    diagonalMap α σ τ hσ hτ (algebraMap A (diagonal A 𝒮 𝒯) a) =
      algebraMap A' (diagonal A' 𝒮' 𝒯') (α a) :=
  Subtype.ext (tensorMap_algebraMap α σ τ hσ hτ a)

theorem tensorMap_tproj (h𝒮 : ∀ a : A, algebraMap A S a ∈ 𝒮 0)
    (h𝒯 : ∀ a : A, algebraMap A T a ∈ 𝒯 0) (h𝒮' : ∀ a : A', algebraMap A' S' a ∈ 𝒮' 0)
    (h𝒯' : ∀ a : A', algebraMap A' T' a ∈ 𝒯' 0) (d : ℕ) (x : S ⊗[A] T) :
    tensorMap α σ τ hσ hτ (tproj 𝒮 𝒯 h𝒮 h𝒯 d x) =
      tproj 𝒮' 𝒯' h𝒮' h𝒯' d (tensorMap α σ τ hσ hτ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [tproj_tmul, tensorMap_tmul, tensorMap_tmul, tproj_tmul,
      GradedRingHom.map_directSumDecompose, GradedRingHom.map_directSumDecompose]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Map

section Functorial

variable {𝒮 𝒯}

variable {A' S' T' : Type*} [CommRing A'] [CommRing S'] [CommRing T'] [Algebra A' S']
  [Algebra A' T'] {𝒮' : ℕ → AddSubgroup S'} {𝒯' : ℕ → AddSubgroup T'} [GradedRing 𝒮']
  [GradedRing 𝒯']
  {A'' S'' T'' : Type*} [CommRing A''] [CommRing S''] [CommRing T''] [Algebra A'' S'']
  [Algebra A'' T''] {𝒮'' : ℕ → AddSubgroup S''} {𝒯'' : ℕ → AddSubgroup T''} [GradedRing 𝒮'']
  [GradedRing 𝒯'']

theorem diagonalMap_id (α : A →+* A) (σ : 𝒮 →+*ᵍ 𝒮) (τ : 𝒯 →+*ᵍ 𝒯)
    (hσ : ∀ a, σ (algebraMap A S a) = algebraMap A S (α a))
    (hτ : ∀ a, τ (algebraMap A T a) = algebraMap A T (α a))
    (hσ' : ∀ s, σ s = s) (hτ' : ∀ t, τ t = t) (x : diagonal A 𝒮 𝒯) :
    diagonalMap α σ τ hσ hτ x = x := by
  refine Subtype.ext ?_
  rw [coe_diagonalMap]
  generalize (x : S ⊗[A] T) = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s t => rw [tensorMap_tmul, hσ', hτ']
  | add x y hx hy => rw [map_add, hx, hy]

theorem diagonalMap_comp (α₁ : A →+* A') (σ₁ : 𝒮 →+*ᵍ 𝒮') (τ₁ : 𝒯 →+*ᵍ 𝒯')
    (hσ₁ : ∀ a, σ₁ (algebraMap A S a) = algebraMap A' S' (α₁ a))
    (hτ₁ : ∀ a, τ₁ (algebraMap A T a) = algebraMap A' T' (α₁ a))
    (α₂ : A' →+* A'') (σ₂ : 𝒮' →+*ᵍ 𝒮'') (τ₂ : 𝒯' →+*ᵍ 𝒯'')
    (hσ₂ : ∀ a, σ₂ (algebraMap A' S' a) = algebraMap A'' S'' (α₂ a))
    (hτ₂ : ∀ a, τ₂ (algebraMap A' T' a) = algebraMap A'' T'' (α₂ a))
    (α₃ : A →+* A'') (σ₃ : 𝒮 →+*ᵍ 𝒮'') (τ₃ : 𝒯 →+*ᵍ 𝒯'')
    (hσ₃ : ∀ a, σ₃ (algebraMap A S a) = algebraMap A'' S'' (α₃ a))
    (hτ₃ : ∀ a, τ₃ (algebraMap A T a) = algebraMap A'' T'' (α₃ a))
    (hσ : ∀ s, σ₃ s = σ₂ (σ₁ s)) (hτ : ∀ t, τ₃ t = τ₂ (τ₁ t)) (x : diagonal A 𝒮 𝒯) :
    diagonalMap α₃ σ₃ τ₃ hσ₃ hτ₃ x =
      diagonalMap α₂ σ₂ τ₂ hσ₂ hτ₂ (diagonalMap α₁ σ₁ τ₁ hσ₁ hτ₁ x) := by
  refine Subtype.ext ?_
  rw [coe_diagonalMap, coe_diagonalMap, coe_diagonalMap]
  generalize (x : S ⊗[A] T) = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s t => rw [tensorMap_tmul, tensorMap_tmul, tensorMap_tmul, hσ, hτ]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

end Functorial

/-! ### Localization -/

section Localization

variable {𝒮 𝒯}

variable {A' S' T' : Type*} [CommRing A'] [CommRing S'] [CommRing T'] [Algebra A' S']
  [Algebra A' T'] {𝒮' : ℕ → AddSubgroup S'} {𝒯' : ℕ → AddSubgroup T'} [GradedRing 𝒮']
  [GradedRing 𝒯'] (α : A →+* A') (σ : 𝒮 →+*ᵍ 𝒮') (τ : 𝒯 →+*ᵍ 𝒯')
  (hσ : ∀ a, σ (algebraMap A S a) = algebraMap A' S' (α a))
  (hτ : ∀ a, τ (algebraMap A T a) = algebraMap A' T' (α a)) (r : A)

omit [GradedRing 𝒮] [GradedRing 𝒯] [GradedRing 𝒮'] [GradedRing 𝒯'] in
/-- If `S' = S[1/r]` and `T' = T[1/r]`, every element of `S' ⊗_{A'} T'` becomes, after
multiplication by a power of `r`, the image of an element of `S ⊗_A T`. -/
theorem tensorMap_surj
    (hS : letI := σ.toRingHom.toAlgebra; IsLocalization.Away (algebraMap A S r) S')
    (hT : letI := τ.toRingHom.toAlgebra; IsLocalization.Away (algebraMap A T r) T')
    (z : S' ⊗[A'] T') : ∃ (y : S ⊗[A] T) (k : ℕ),
      z * algebraMap A' (S' ⊗[A'] T') (α r) ^ k = tensorMap α σ τ hσ hτ y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul s' t' =>
    let := σ.toRingHom.toAlgebra
    let := τ.toRingHom.toAlgebra
    obtain ⟨⟨s, _, a, rfl⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A S r)) s'
    obtain ⟨⟨t, _, b, rfl⟩, ht⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A T r)) t'
    have hs' : s' * σ (algebraMap A S r) ^ a = σ s := by rw [← map_pow]; exact hs
    have ht' : t' * τ (algebraMap A T r) ^ b = τ t := by rw [← map_pow]; exact ht
    have hX1 : algebraMap A' (S' ⊗[A'] T') (α r) = σ (algebraMap A S r) ⊗ₜ 1 := by
      rw [hσ, Algebra.TensorProduct.algebraMap_apply]
    have hX2 : algebraMap A' (S' ⊗[A'] T') (α r) = 1 ⊗ₜ τ (algebraMap A T r) := by
      rw [hτ, Algebra.TensorProduct.algebraMap_apply']
    refine ⟨s ⊗ₜ t, a + b, ?_⟩
    calc (s' ⊗ₜ t') * algebraMap A' (S' ⊗[A'] T') (α r) ^ (a + b)
        = (s' ⊗ₜ t') * ((σ (algebraMap A S r) ⊗ₜ[A'] (1 : T')) ^ a *
            ((1 : S') ⊗ₜ[A'] τ (algebraMap A T r)) ^ b) := by
          rw [pow_add, ← hX1, ← hX2]
      _ = (s' * σ (algebraMap A S r) ^ a) ⊗ₜ (t' * τ (algebraMap A T r) ^ b) := by
          simp [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
      _ = tensorMap α σ τ hσ hτ (s ⊗ₜ t) := by rw [hs', ht', tensorMap_tmul]
  | add z w hz hw =>
    obtain ⟨y₁, k₁, h₁⟩ := hz
    obtain ⟨y₂, k₂, h₂⟩ := hw
    refine ⟨y₁ * algebraMap A _ r ^ k₂ + y₂ * algebraMap A _ r ^ k₁, k₁ + k₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, tensorMap_algebraMap, ← h₁, ← h₂]
    ring

omit [GradedRing 𝒮] [GradedRing 𝒯] [GradedRing 𝒮'] [GradedRing 𝒯'] in
/-- If `A' = A[1/r]`, `S' = S[1/r]` and `T' = T[1/r]`, an element of `S ⊗_A T` whose image in
`S' ⊗_{A'} T'` vanishes is killed by a power of `r`. -/
theorem tensorMap_exists_of_eq (hA : letI := α.toAlgebra; IsLocalization.Away r A')
    (hS : letI := σ.toRingHom.toAlgebra; IsLocalization.Away (algebraMap A S r) S')
    (hT : letI := τ.toRingHom.toAlgebra; IsLocalization.Away (algebraMap A T r) T')
    {x y : S ⊗[A] T} (h : tensorMap α σ τ hσ hτ x = tensorMap α σ τ hσ hτ y) :
    ∃ k : ℕ, algebraMap A (S ⊗[A] T) r ^ k * x = algebraMap A (S ⊗[A] T) r ^ k * y := by
  let Rr := Localization.Away (algebraMap A (S ⊗[A] T) r)
  have hu : IsUnit (algebraMap (S ⊗[A] T) Rr (algebraMap A (S ⊗[A] T) r)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let := α.toAlgebra
  let := σ.toRingHom.toAlgebra
  let := τ.toRingHom.toAlgebra
  let ψA : A' →+* Rr :=
    IsLocalization.Away.lift r (g := (algebraMap (S ⊗[A] T) Rr).comp (algebraMap A _)) hu
  let ψS : S' →+* Rr := IsLocalization.Away.lift (algebraMap A S r)
    (g := (algebraMap (S ⊗[A] T) Rr).comp Algebra.TensorProduct.includeLeftRingHom)
    (by
      change IsUnit (algebraMap (S ⊗[A] T) Rr (algebraMap A S r ⊗ₜ 1))
      rw [← Algebra.TensorProduct.algebraMap_apply]
      exact hu)
  let ψT : T' →+* Rr := IsLocalization.Away.lift (algebraMap A T r)
    (g := (algebraMap (S ⊗[A] T) Rr).comp Algebra.TensorProduct.includeRight.toRingHom)
    (by
      change IsUnit (algebraMap (S ⊗[A] T) Rr (1 ⊗ₜ algebraMap A T r))
      rw [← Algebra.TensorProduct.algebraMap_apply']
      exact hu)
  let : Algebra A' Rr := ψA.toAlgebra
  have hψS : ψS.comp (algebraMap A' S') = ψA := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext a
    change ψS (algebraMap A' S' (α a)) = ψA (algebraMap A A' a)
    rw [← hσ]
    change ψS (algebraMap S S' (algebraMap A S a)) = _
    rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hψT : ψT.comp (algebraMap A' T') = ψA := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext a
    change ψT (algebraMap A' T' (α a)) = ψA (algebraMap A A' a)
    rw [← hτ]
    change ψT (algebraMap T T' (algebraMap A T a)) = _
    rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
    simp
  let Ψ : S' ⊗[A'] T' →ₐ[A'] Rr := Algebra.TensorProduct.lift (R := A') (S := A')
    ({ toRingHom := ψS, commutes' := fun a => congr($hψS a) } : S' →ₐ[A'] Rr)
    ({ toRingHom := ψT, commutes' := fun a => congr($hψT a) } : T' →ₐ[A'] Rr)
    (fun _ _ => Commute.all _ _)
  have hΨ : ∀ z, Ψ (tensorMap α σ τ hσ hτ z) = algebraMap (S ⊗[A] T) Rr z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s t =>
      rw [tensorMap_tmul, Algebra.TensorProduct.lift_tmul]
      change ψS (algebraMap S S' s) * ψT (algebraMap T T' t) = _
      rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
      simp [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]
  have := congrArg Ψ h
  rw [hΨ, hΨ] at this
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap A (S ⊗[A] T) r)) this
  exact ⟨k, hk⟩

/-- **Localization of diagonal products.** If `A' = A[1/r]`, `S' = S[1/r]` and `T' = T[1/r]`
compatibly, then `S' ×_{A'} T' = (S ×_A T)[1/r]`. -/
theorem isLocalizationAway_diagonalMap (h𝒮 : ∀ a : A, algebraMap A S a ∈ 𝒮 0)
    (h𝒯 : ∀ a : A, algebraMap A T a ∈ 𝒯 0) (h𝒮' : ∀ a : A', algebraMap A' S' a ∈ 𝒮' 0)
    (h𝒯' : ∀ a : A', algebraMap A' T' a ∈ 𝒯' 0)
    (hA : letI := α.toAlgebra; IsLocalization.Away r A')
    (hS : letI := σ.toRingHom.toAlgebra; IsLocalization.Away (algebraMap A S r) S')
    (hT : letI := τ.toRingHom.toAlgebra; IsLocalization.Away (algebraMap A T r) T') :
    letI := (diagonalMap α σ τ hσ hτ).toAlgebra
    IsLocalization.Away (algebraMap A (diagonal A 𝒮 𝒯) r) (diagonal A' 𝒮' 𝒯') := by
  let := (diagonalMap α σ τ hσ hτ).toAlgebra
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow, diagonalMap_algebraMap]
    let := α.toAlgebra
    exact ((IsLocalization.Away.algebraMap_isUnit r : IsUnit (algebraMap A A' r)).map
      (algebraMap A' (diagonal A' 𝒮' 𝒯'))).pow k
  · classical
    intro z
    obtain ⟨y, k, hy⟩ := tensorMap_surj α σ τ hσ hτ r hS hT (z : S' ⊗[A'] T')
    let := gradedRing A' 𝒮' 𝒯' h𝒮' h𝒯'
    let w : diagonal A' 𝒮' 𝒯' := z * algebraMap A' _ (α r) ^ k
    have hw : (w : S' ⊗[A'] T') = tensorMap α σ τ hσ hτ y := by
      rw [← hy]
      simp [w]
    let F := (decompose (grading A' 𝒮' 𝒯') w).support
    have hyD : ∑ d ∈ F, tproj 𝒮 𝒯 h𝒮 h𝒯 d y ∈ diagonal A 𝒮 𝒯 :=
      Subalgebra.sum_mem _ fun d _ => mem_diagonal_of_mem (tproj_mem 𝒮 𝒯 h𝒮 h𝒯 d y)
    refine ⟨(⟨_, hyD⟩, ⟨algebraMap A _ r ^ k, k, rfl⟩), Subtype.ext ?_⟩
    change ((z * diagonalMap α σ τ hσ hτ (algebraMap A _ r ^ k) : diagonal A' 𝒮' 𝒯') :
      S' ⊗[A'] T') = tensorMap α σ τ hσ hτ (∑ d ∈ F, tproj 𝒮 𝒯 h𝒮 h𝒯 d y)
    rw [map_pow, diagonalMap_algebraMap, map_sum]
    change (w : S' ⊗[A'] T') = _
    have key : (w : S' ⊗[A'] T') =
        ∑ d ∈ F, ((decompose (grading A' 𝒮' 𝒯') w d : diagonal A' 𝒮' 𝒯') : S' ⊗[A'] T') := by
      conv_lhs => rw [← DirectSum.sum_support_decompose (grading A' 𝒮' 𝒯') w]
      push_cast
      rfl
    rw [key]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coe_decompose 𝒮' 𝒯' h𝒮' h𝒯', hw, tensorMap_tproj α σ τ hσ hτ h𝒮 h𝒯 h𝒮' h𝒯']
  · intro x y hxy
    have h : tensorMap α σ τ hσ hτ x = tensorMap α σ τ hσ hτ y := congrArg Subtype.val hxy
    obtain ⟨k, hk⟩ := tensorMap_exists_of_eq α σ τ hσ hτ r hA hS hT h
    exact ⟨⟨algebraMap A _ r ^ k, k, rfl⟩, Subtype.ext (by simpa using hk)⟩

end Localization

end SegreProduct

end Hartshorne
