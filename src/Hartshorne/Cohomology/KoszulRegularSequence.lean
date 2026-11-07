/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.KoszulComplex
import Hartshorne.Scheme.ExteriorPowerFiltrationAlgebra
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-!
# The Koszul complex of a regular sequence

If `f₁, …, f_r` is a regular sequence on an `A`-module `M`, then the Koszul complex
`K_•(f₁, …, f_r; M)` is exact in positive degrees and the augmentation identifies `H_0` with
`M / (f₁, …, f_r) M` (Hartshorne, *Algebraic Geometry*, III.7, Proposition 7.10A, citing
Matsumura, *Commutative Algebra*, Theorem 43; Stacks Project, tag 062D). "Regular sequence" is
Mathlib's `RingTheory.Sequence.IsWeaklyRegular`: each `fᵢ` is a non-zero-divisor on
`M / (f₁, …, f_{i-1}) M`, with no condition `(f₁, …, f_r) M ≠ M` (which would only strengthen
the hypothesis).

The proof is by induction on `r`, splitting off the last element. Writing `A^{r+1} = A^r × A`,
the Koszul complex of `(f', a)` decomposes degreewise as
`⋀^{p+1}(A^r × A) = ⋀^{p+1} A^r ⊕ e ∧ ⋀^p A^r` with `e = (0, 1)`
(`exteriorAlgebra_prod_decomp`), and its differential is `d ∘ i = i ∘ d'`,
`d (e ∧ y) = a y - e ∧ d' y`: it is the mapping cone of multiplication by `a` on
`K_•(f'; M)`. A diagram chase (`exact_of_cone`) then gives exactness from the exactness of
`K_•(f'; M)` and the injectivity of `a` on `M / (f') M = H_0(K_•(f'; M))`.

Main results:
* `sequenceKoszulComplex_exactAt_of_isWeaklyRegular`,
  `isZero_sequenceKoszulComplex_homology_of_isWeaklyRegular`: `H_p(K_•(f; M)) = 0` for `p > 0`;
* `sequenceKoszulAugmentation`, `quasiIso_sequenceKoszulAugmentation`: the augmentation
  `K_•(f; M) → M / (f₁, …, f_r) M` is a quasi-isomorphism (a Koszul resolution).
-/

universe u

open ExteriorAlgebra TensorProduct CategoryTheory

namespace Hartshorne

namespace Koszul

open ExteriorPowerFiltration (coe_exteriorPower_map)

variable {A : Type u} [CommRing A]

section ExteriorAlgebra

variable {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]

lemma contractLeft_map (P : W →ₗ[A] V) (d : Module.Dual A V) (x : ExteriorAlgebra A W) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map P x) =
      ExteriorAlgebra.map P (CliffordAlgebra.contractLeft (d ∘ₗ P) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι_mul, hx, map_sub, map_smul, map_mul,
      ExteriorAlgebra.map_apply_ι, LinearMap.comp_apply]

lemma contractLeft_eq_zero_of_mem_zero (d : Module.Dual A V) {x : ExteriorAlgebra A V}
    (hx : x ∈ ⋀[A]^0 V) : CliffordAlgebra.contractLeft d x = 0 := by
  rw [exteriorPower, pow_zero, Submodule.mem_one] at hx
  obtain ⟨r, rfl⟩ := hx
  simp [CliffordAlgebra.contractLeft_algebraMap]

/-- Left multiplication by `ι e` raises degrees in the exterior algebra by one. -/
lemma ι_mul_mem_exteriorPower (e : V) {n : ℕ} {x : ExteriorAlgebra A V} (hx : x ∈ ⋀[A]^n V) :
    ι A e * x ∈ ⋀[A]^(n + 1) V := by
  rw [exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ e) hx

/-- Exterior multiplication on the left by `e`, `⋀^n V → ⋀^{n+1} V`. -/
noncomputable def wedgeLeft (e : V) (n : ℕ) : ⋀[A]^n V →ₗ[A] ⋀[A]^(n + 1) V :=
  ((LinearMap.mulLeft A (ι A e)).comp (⋀[A]^n V).subtype).codRestrict _
    fun x => ι_mul_mem_exteriorPower e x.2

@[simp]
lemma coe_wedgeLeft (e : V) (n : ℕ) (x : ⋀[A]^n V) :
    (wedgeLeft e n x : ExteriorAlgebra A V) = ι A e * x := rfl

end ExteriorAlgebra

section Cone

variable {W : Type*} [AddCommGroup W] [Module A W]

/-- The decomposition of the exterior algebra of `W × A` along `W × A = W ⊕ A e`,
`e = (0, 1)`: every `x` equals `P x + e ∧ P (ι_ψ x)`, where `P = inl ∘ fst` and `ψ = snd`. -/
lemma exteriorAlgebra_prod_decomp (x : ExteriorAlgebra A (W × A)) :
    ExteriorAlgebra.map (LinearMap.inl A W A ∘ₗ LinearMap.fst A W A) x +
      ι A ((0 : W), (1 : A)) * ExteriorAlgebra.map (LinearMap.inl A W A ∘ₗ LinearMap.fst A W A)
        (CliffordAlgebra.contractLeft (LinearMap.snd A W A) x) = x := by
  set P := LinearMap.inl A W A ∘ₗ LinearMap.fst A W A
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, mul_add]
    conv_rhs => rw [← hx, ← hy]
    abel
  | ι_mul x m hx =>
    have hm : ι A m = ι A (P m) + m.2 • ι A ((0 : W), (1 : A)) := by
      rw [← map_smul, ← map_add]
      congr 1
      ext <;> simp [P]
    have hee : ι A ((0 : W), (1 : A)) * ι A ((0 : W), (1 : A)) = 0 := ExteriorAlgebra.ι_sq_zero _
    have hanti : ι A ((0 : W), (1 : A)) * ι A (P m) = -(ι A (P m) * ι A ((0 : W), (1 : A))) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul, map_sub,
      map_smul, map_mul, ExteriorAlgebra.map_apply_ι]
    conv_rhs => rw [← hx, hm]
    simp only [LinearMap.snd_apply, mul_add, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      ← mul_assoc, hee, hanti, neg_mul, smul_zero, add_zero]
    abel

/-- The linear form on `W × A` extending `φ'` on `W` by `a` on the new basis vector `(0, 1)`:
`(w, t) ↦ φ'(w) + a t`. -/
noncomputable def extendForm (φ' : Module.Dual A W) (a : A) : Module.Dual A (W × A) :=
  φ'.coprod (a • LinearMap.id)

@[simp]
lemma extendForm_apply (φ' : Module.Dual A W) (a : A) (x : W × A) :
    extendForm φ' a x = φ' x.1 + a * x.2 := rfl

lemma extendForm_comp_inl (φ' : Module.Dual A W) (a : A) :
    extendForm φ' a ∘ₗ LinearMap.inl A W A = φ' := by
  ext; simp

/-- The inclusion `⋀^n W → ⋀^n (W × A)`. -/
noncomputable abbrev coneIncl (n : ℕ) : ⋀[A]^n W →ₗ[A] ⋀[A]^n (W × A) :=
  exteriorPower.map n (LinearMap.inl A W A)

/-- The projection `⋀^n (W × A) → ⋀^n W`. -/
noncomputable abbrev coneProj (n : ℕ) : ⋀[A]^n (W × A) →ₗ[A] ⋀[A]^n W :=
  exteriorPower.map n (LinearMap.fst A W A)

/-- The map `⋀^n W → ⋀^{n+1} (W × A)`, `x ↦ e ∧ x` with `e = (0, 1)`. -/
noncomputable def coneSection (n : ℕ) : ⋀[A]^n W →ₗ[A] ⋀[A]^(n + 1) (W × A) :=
  wedgeLeft ((0 : W), (1 : A)) n ∘ₗ coneIncl n

/-- The map `⋀^{n+1} (W × A) → ⋀^n W`, contraction by the last coordinate followed by the
projection. -/
noncomputable def coneQuot (n : ℕ) : ⋀[A]^(n + 1) (W × A) →ₗ[A] ⋀[A]^n W :=
  coneProj n ∘ₗ contraction (LinearMap.snd A W A) n

lemma coneProj_comp_coneIncl (n : ℕ) :
    coneProj (A := A) (W := W) n ∘ₗ coneIncl n = LinearMap.id := by
  rw [← exteriorPower.map_comp, LinearMap.fst_comp_inl, exteriorPower.map_id]

lemma coneIncl_comp_coneProj_add (n : ℕ) :
    coneIncl (A := A) (W := W) (n + 1) ∘ₗ coneProj (n + 1) + coneSection n ∘ₗ coneQuot n =
      LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, Submodule.coe_add,
    coneSection, coneQuot, coe_wedgeLeft, coe_exteriorPower_map, coe_contraction]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    exteriorAlgebra_prod_decomp]

lemma coneQuot_comp_coneIncl (n : ℕ) :
    coneQuot (A := A) (W := W) n ∘ₗ coneIncl (n + 1) = 0 := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero, coneQuot,
    coe_exteriorPower_map, coe_contraction, contractLeft_map, LinearMap.snd_comp_inl, map_zero,
    LinearMap.zero_apply]

lemma coneQuot_comp_coneSection (n : ℕ) :
    coneQuot (A := A) (W := W) n ∘ₗ coneSection n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.id_apply, coneQuot, coneSection,
    coe_exteriorPower_map, coe_contraction, coe_wedgeLeft, CliffordAlgebra.contractLeft_ι_mul,
    contractLeft_map, LinearMap.snd_comp_inl, map_zero, LinearMap.zero_apply, mul_zero, sub_zero,
    LinearMap.snd_apply, one_smul]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, LinearMap.fst_comp_inl,
    ExteriorAlgebra.map_id, AlgHom.id_apply]

variable (φ' : Module.Dual A W) (a : A)

lemma contraction_extendForm_comp_coneIncl (n : ℕ) :
    contraction (extendForm φ' a) n ∘ₗ coneIncl (n + 1) = coneIncl n ∘ₗ contraction φ' n := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, contraction_map, extendForm_comp_inl]

lemma contraction_extendForm_comp_coneSection_zero :
    contraction (extendForm φ' a) 0 ∘ₗ coneSection 0 = a • coneIncl 0 := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_smul, coneSection,
    coe_exteriorPower_map, coe_contraction, coe_wedgeLeft, CliffordAlgebra.contractLeft_ι_mul,
    contractLeft_map, extendForm_apply, mul_one, zero_add, map_zero]
  rw [contractLeft_eq_zero_of_mem_zero _ x.2, map_zero, mul_zero, sub_zero]

lemma contraction_extendForm_comp_coneSection_succ (n : ℕ) :
    contraction (extendForm φ' a) (n + 1) ∘ₗ coneSection (n + 1) =
      a • coneIncl (n + 1) - coneSection n ∘ₗ contraction φ' n := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_sub,
    Submodule.coe_smul, coneSection, coe_exteriorPower_map, coe_contraction, coe_wedgeLeft,
    CliffordAlgebra.contractLeft_ι_mul, contractLeft_map, extendForm_apply, mul_one, zero_add,
    map_zero, extendForm_comp_inl]

end Cone

section Chase

/-- The diagram chase behind the inductive step. Let `K'` and `K` be chain complexes of modules
indexed by `ℕ` (differentials `d'` and `d`), with degreewise maps `i : K' → K` (split by `r`) and
`s : K'_k → K_{k+1}`, `q : K_{k+1} → K'_k` exhibiting `K_{k+1} = i(K'_{k+1}) ⊕ s(K'_k)`, such that
`d ∘ i = i ∘ d'` and `d ∘ s = a • i - s ∘ d'` (so `K` is the mapping cone of multiplication by `a`
on `K'`). If `K'` is exact in positive degrees and `a` is a non-zero-divisor on `H_0(K')`, then `K`
is exact in positive degrees. -/
theorem exact_of_cone {K' K : ℕ → Type*} [∀ k, AddCommGroup (K' k)] [∀ k, Module A (K' k)]
    [∀ k, AddCommGroup (K k)] [∀ k, Module A (K k)]
    (d' : ∀ k, K' (k + 1) →ₗ[A] K' k) (d : ∀ k, K (k + 1) →ₗ[A] K k)
    (i : ∀ k, K' k →ₗ[A] K k) (r : ∀ k, K k →ₗ[A] K' k) (s : ∀ k, K' k →ₗ[A] K (k + 1))
    (q : ∀ k, K (k + 1) →ₗ[A] K' k) (a : A)
    (hdd : ∀ k z, d k (d (k + 1) z) = 0) (hri : ∀ k x, r k (i k x) = x)
    (hdec : ∀ k z, i (k + 1) (r (k + 1) z) + s k (q k z) = z)
    (hqi : ∀ k x, q k (i (k + 1) x) = 0) (hqs : ∀ k y, q k (s k y) = y)
    (hdi : ∀ k x, d k (i (k + 1) x) = i k (d' k x))
    (hds0 : ∀ y, d 0 (s 0 y) = a • i 0 y)
    (hds : ∀ k y, d (k + 1) (s (k + 1) y) = a • i (k + 1) y - s k (d' k y))
    (hexact : ∀ k, Function.Exact (d' (k + 1)) (d' k))
    (hreg : ∀ y, a • y ∈ LinearMap.range (d' 0) → y ∈ LinearMap.range (d' 0)) (n : ℕ) :
    Function.Exact (d (n + 1)) (d n) := by
  have hinj : ∀ k, Function.Injective (i k) := fun k =>
    Function.LeftInverse.injective (g := r k) (hri k)
  intro z
  refine ⟨fun hz => ?_, ?_⟩
  swap
  · rintro ⟨w, rfl⟩
    exact hdd n w
  obtain ⟨w, hw⟩ : ∃ w, d' n w = q n z := by
    cases n with
    | zero =>
      have h1 : i 0 (d' 0 (r 1 z) + a • q 0 z) = 0 := by
        rw [map_add, map_smul, ← hdi, ← hds0, ← map_add, hdec]
        exact hz
      have h2 : d' 0 (r 1 z) + a • q 0 z = 0 := hinj 0 (h1.trans (map_zero _).symm)
      exact hreg _ ⟨-(r 1 z), by rw [map_neg, neg_eq_iff_add_eq_zero]; exact h2⟩
    | succ m =>
      have h1 : q m (d (m + 1) z) = -d' m (q (m + 1) z) := by
        conv_lhs => rw [← hdec (m + 1) z]
        rw [map_add, hdi, hds, map_add, map_sub, map_smul, hqi, hqi, hqs, smul_zero, zero_add,
          zero_sub]
      rw [hz, map_zero, eq_comm, neg_eq_zero] at h1
      exact (hexact m _).1 h1
  have hz' : z + d (n + 1) (s (n + 1) w) = i (n + 1) (r (n + 1) z + a • w) := by
    rw [hds, hw, map_add, map_smul]
    nth_rewrite 1 [← hdec n z]
    abel
  have hc : d' n (r (n + 1) z + a • w) = 0 := by
    apply hinj n
    rw [map_zero, ← hdi, ← hz', map_add, hz, hdd, add_zero]
  obtain ⟨u, hu⟩ := (hexact n _).1 hc
  refine ⟨i (n + 2) u - s (n + 1) w, ?_⟩
  rw [map_sub, hdi, hu, ← hz', add_sub_cancel_right]

end Chase

section Exactness

variable {W : Type u} [AddCommGroup W] [Module A W] (M : Type*) [AddCommGroup M] [Module A M]

lemma mem_range_rTensor_contraction_zero_iff {V : Type u} [AddCommGroup V] [Module A V]
    (φ : Module.Dual A V) (y : ⋀[A]^0 V ⊗[A] M) :
    y ∈ LinearMap.range ((contraction φ 0).rTensor M) ↔
      degreeZeroEquiv M y ∈ koszulSubmodule φ M := by
  rw [← range_degreeZeroEquiv_comp_contraction]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (degreeZeroEquiv M).injective hz⟩

/-- The inductive step: if `K(φ'; M)` is exact in positive degrees and `a` is a non-zero-divisor
on `M / I M`, `I = φ'(W)`, then `K(φ' + a; M)` on `W × A` is exact in positive degrees. -/
theorem exact_contraction_extendForm (φ' : Module.Dual A W) (a : A)
    (hexact : ∀ n, Function.Exact ((contraction φ' (n + 1)).rTensor M)
      ((contraction φ' n).rTensor M))
    (hreg : ∀ m : M, a • m ∈ koszulSubmodule φ' M → m ∈ koszulSubmodule φ' M) (n : ℕ) :
    Function.Exact ((contraction (extendForm φ' a) (n + 1)).rTensor M)
      ((contraction (extendForm φ' a) n).rTensor M) := by
  refine exact_of_cone (K' := fun k => ⋀[A]^k W ⊗[A] M) (K := fun k => ⋀[A]^k (W × A) ⊗[A] M)
    (fun k => (contraction φ' k).rTensor M) (fun k => (contraction (extendForm φ' a) k).rTensor M)
    (fun k => (coneIncl k).rTensor M) (fun k => (coneProj k).rTensor M)
    (fun k => (coneSection k).rTensor M) (fun k => (coneQuot k).rTensor M) a ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hexact ?_ n
  · intro k z
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, contraction_comp_contraction,
      LinearMap.rTensor_zero, LinearMap.zero_apply]
  · intro k x
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, coneProj_comp_coneIncl,
      LinearMap.rTensor_id, LinearMap.id_apply]
  · intro k z
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.add_apply,
      ← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_add,
      coneIncl_comp_coneProj_add, LinearMap.rTensor_id, LinearMap.id_apply]
  · intro k x
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, coneQuot_comp_coneIncl,
      LinearMap.rTensor_zero, LinearMap.zero_apply]
  · intro k y
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, coneQuot_comp_coneSection,
      LinearMap.rTensor_id, LinearMap.id_apply]
  · intro k x
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      ← LinearMap.rTensor_comp, contraction_extendForm_comp_coneIncl]
  · intro y
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      contraction_extendForm_comp_coneSection_zero, LinearMap.rTensor_smul, LinearMap.smul_apply]
  · intro k y
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      contraction_extendForm_comp_coneSection_succ, LinearMap.rTensor_sub, LinearMap.rTensor_smul,
      LinearMap.rTensor_comp]
    rfl
  · intro y hy
    rw [mem_range_rTensor_contraction_zero_iff] at hy ⊢
    rw [map_smul] at hy
    exact hreg _ hy

end Exactness

section Complex

variable {V : Type u} [AddCommGroup V] [Module A V]

/-- Exactness of the Koszul complex at `K_{n+1}` in terms of the contraction differentials. -/
lemma koszulComplex_exactAt_succ_iff (φ : Module.Dual A V) (M : ModuleCat.{u} A) (n : ℕ) :
    (koszulComplex φ M).ExactAt (n + 1) ↔
      Function.Exact ((contraction φ (n + 1)).rTensor M) ((contraction φ n).rTensor M) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact ((koszulComplex φ M).d (n + 1 + 1) (n + 1)).hom
    ((koszulComplex φ M).d (n + 1) n).hom ↔ _
  rw [koszulComplex_d, koszulComplex_d]
  rfl

variable {W : Type u} [AddCommGroup W] [Module A W]

/-- The inductive step on complexes: if `K(φ'; M)` is exact in positive degrees and `a` is a
non-zero-divisor on `M / I M`, `I = φ'(W)`, then so is `K(φ' + a; M)` on `W × A`. -/
theorem koszulComplex_extendForm_exactAt (φ' : Module.Dual A W) (a : A) (M : ModuleCat.{u} A)
    (hexact : ∀ n, (koszulComplex φ' M).ExactAt (n + 1))
    (hreg : ∀ m : M, a • m ∈ koszulSubmodule φ' M → m ∈ koszulSubmodule φ' M) (n : ℕ) :
    (koszulComplex (extendForm φ' a) M).ExactAt (n + 1) := by
  simp only [koszulComplex_exactAt_succ_iff] at hexact ⊢
  exact exact_contraction_extendForm M φ' a hexact hreg n

end Complex

section Sequence

/-- The linear equivalence `A^r × A ≃ A^{r+1}`, `(g, t) ↦ (g₁, …, g_r, t)`. -/
noncomputable def snocLinearEquiv (r : ℕ) : ((Fin r → A) × A) ≃ₗ[A] (Fin (r + 1) → A) where
  toFun x := Fin.snoc (α := fun _ => A) x.1 x.2
  invFun h := (Fin.init h, h (Fin.last r))
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  left_inv x := by simp
  right_inv h := Fin.snoc_init_self h

lemma koszulForm_comp_snocLinearEquiv {r : ℕ} (f : Fin (r + 1) → A) :
    koszulForm f ∘ₗ (snocLinearEquiv r).toLinearMap =
      extendForm (koszulForm fun i => f i.castSucc) (f (Fin.last r)) := by
  refine LinearMap.ext fun x => ?_
  simp [snocLinearEquiv, koszulForm_apply, Fin.sum_univ_castSucc, mul_comm]

lemma koszulSubmodule_koszulForm {r : ℕ} (f : Fin r → A) (M : Type*) [AddCommGroup M]
    [Module A M] :
    koszulSubmodule (koszulForm f) M = (Ideal.span (Set.range f) • ⊤ : Submodule A M) := by
  rw [koszulSubmodule, range_koszulForm]

lemma ofList_ofFn {r : ℕ} (f : Fin r → A) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  simp only [Ideal.ofList, List.mem_ofFn']
  rfl

lemma subsingleton_exteriorPower_succ_of_subsingleton (V : Type*) [AddCommGroup V] [Module A V]
    [Subsingleton V] (n : ℕ) : Subsingleton (⋀[A]^(n + 1) V) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A (n + 1))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    exact (exteriorPower.ιMulti A (n + 1)).map_coord_zero 0 (Subsingleton.elim _ _)
  | zero => rfl
  | add _ _ _ _ hx hy => rw [hx, hy, add_zero]
  | smul c _ _ hx => rw [hx, smul_zero]

/-- If `f₁, …, f_r` is a (weakly) regular sequence on `M`, then the Koszul complex `K_•(f; M)` is
exact in every positive degree. -/
theorem sequenceKoszulComplex_exactAt_of_isWeaklyRegular :
    ∀ {r : ℕ} (f : Fin r → A) (M : ModuleCat.{u} A),
      RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f) →
        ∀ n, (sequenceKoszulComplex f M).ExactAt (n + 1)
  | 0, f, M, _, n => by
    refine HomologicalComplex.ExactAt.of_isZero ?_
    have := subsingleton_exteriorPower_succ_of_subsingleton (A := A) (Fin 0 → A) n
    exact ModuleCat.isZero_of_subsingleton (ModuleCat.of A (⋀[A]^(n + 1) (Fin 0 → A) ⊗[A] M))
  | r + 1, f, M, hf, n => by
    rw [List.ofFn_succ', List.concat_eq_append, RingTheory.Sequence.isWeaklyRegular_append_iff,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hf
    obtain ⟨h1, h2⟩ := hf
    refine HomologicalComplex.ExactAt.of_iso ?_
      (koszulChangeOfBasisIso (snocLinearEquiv r) (koszulForm_comp_snocLinearEquiv f) M)
    refine koszulComplex_extendForm_exactAt _ _ M
      (sequenceKoszulComplex_exactAt_of_isWeaklyRegular _ M h1) (fun m hm => ?_) n
    rw [koszulSubmodule_koszulForm, ← ofList_ofFn] at hm ⊢
    have := h2 (show f (Fin.last r) • (Submodule.Quotient.mk m : M ⧸ _) = f (Fin.last r) • 0 by
      rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hm)
    exact (Submodule.Quotient.mk_eq_zero _).1 this

/-- **Hartshorne III.7, Proposition 7.10A** (vanishing): if `f₁, …, f_r` is a regular sequence on
an `A`-module `M` (each `fᵢ` a non-zero-divisor on `M / (f₁, …, f_{i-1}) M`), then
`H_p(K_•(f; M)) = 0` for `p > 0`. -/
theorem isZero_sequenceKoszulComplex_homology_of_isWeaklyRegular {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{u} A) (hf : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f)) {p : ℕ}
    (hp : 0 < p) : Limits.IsZero ((sequenceKoszulComplex f M).homology p) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  exact (sequenceKoszulComplex_exactAt_of_isWeaklyRegular f M hf n).isZero_homology

/-- The augmentation `K_•(f; M) → M / (f₁, …, f_r) M`, as a chain map to the complex concentrated
in degree `0`. -/
noncomputable def sequenceKoszulAugmentation {r : ℕ} (f : Fin r → A) (M : ModuleCat.{u} A) :
    sequenceKoszulComplex f M ⟶ (ChainComplex.single₀ (ModuleCat.{u} A)).obj
      (ModuleCat.of A (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule A M))) :=
  ((sequenceKoszulComplex f M).toSingle₀Equiv _).symm
    ⟨koszulAugmentation (koszulForm f) M ≫
      (Submodule.quotEquivOfEq _ _ (koszulSubmodule_koszulForm f M)).toModuleIso.hom, by
      rw [koszulComplex_d_comp_koszulAugmentation_assoc, Limits.zero_comp]⟩

/-- **Hartshorne III.7, Proposition 7.10A** (Koszul resolution): if `f₁, …, f_r` is a regular
sequence on `M`, the augmentation `K_•(f; M) → M / (f₁, …, f_r) M` is a quasi-isomorphism; that
is, `H_p(K_•(f; M)) = 0` for `p > 0` and the augmentation induces
`H_0(K_•(f; M)) ≅ M / (f₁, …, f_r) M`. -/
theorem quasiIso_sequenceKoszulAugmentation {r : ℕ} (f : Fin r → A) (M : ModuleCat.{u} A)
    (hf : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f)) :
    QuasiIso (sequenceKoszulAugmentation f M) where
  quasiIsoAt m := by
    cases m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _
        (HomologicalComplex.shape (sequenceKoszulComplex f M) 0 0 (by simp)) rfl rfl]
      constructor
      · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
        change Function.Exact ((contraction (koszulForm f) 0).rTensor M)
          ((Submodule.quotEquivOfEq _ _ (koszulSubmodule_koszulForm f M)) ∘
            augmentationLinearMap (koszulForm f) M)
        exact (exact_contraction_augmentationLinearMap (koszulForm f) M).comp_injective _
          (LinearEquiv.injective _) (map_zero _)
      · rw [ModuleCat.epi_iff_surjective]
        change Function.Surjective ((Submodule.quotEquivOfEq _ _ (koszulSubmodule_koszulForm f M)) ∘
            augmentationLinearMap (koszulForm f) M)
        exact (LinearEquiv.surjective _).comp (augmentationLinearMap_surjective _ _)
    | succ m =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact sequenceKoszulComplex_exactAt_of_isWeaklyRegular f M hf m

end Sequence

end Koszul

end Hartshorne
