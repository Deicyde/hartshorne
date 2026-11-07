/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The Koszul complex

The Koszul complex of a sequence `f₁, …, f_r` in a commutative ring `A` with coefficients in an
`A`-module `M` is the homological complex `K_p(f; M) = ⋀^p (A^r) ⊗_A M` whose differential is the
alternating contraction
`d(e_{i₀} ∧ ⋯ ∧ e_{iₚ} ⊗ m) = ∑ⱼ (-1)ʲ e_{i₀} ∧ ⋯ ∧ ê_{iⱼ} ∧ ⋯ ∧ e_{iₚ} ⊗ f_{iⱼ} m`
(Hartshorne, *Algebraic Geometry*, III.7, p.245; Stacks Project, Section 15.29, tag 0621).

We work more generally with a linear form `φ : V → A` on an `A`-module `V`: the contraction by
`φ` in the exterior algebra (`CliffordAlgebra.contractLeft`) lowers degrees by one and squares to
zero, giving `koszulComplex φ M` with `K_p = ⋀^p V ⊗_A M`. For `V = A^r` and `φ(eᵢ) = fᵢ`
(`koszulForm f`) this is `sequenceKoszulComplex f M`.

Main constructions:
* `contraction`, `contraction_contraction` (`d² = 0`), `contraction_ιMulti` (the alternating
  formula), and `koszulComplex`, `koszulComplex_d_tmul_ιMulti`, `sequenceKoszulComplex_d_basis`;
* the augmentation `koszulAugmentation : K_0 → M / I M` with `I = φ(V)`, exact at `K_0`
  (`koszulAugmentationIsCokernel`), and `koszulHomologyZeroIso : H_0 ≅ M / I M`
  (`sequenceKoszulHomologyZeroIso : H_0(K(f; M)) ≅ M / (f₁, …, f_r) M`);
* functoriality in the coefficient module, `koszulFunctor`, with the augmentation natural
  (`koszulMap_f_zero_comp_koszulAugmentation`);
* change of basis: a linear map `P : W → V` with `φ ∘ P = ψ` induces the chain map
  `⋀^• P ⊗ M : K(ψ; M) → K(φ; M)` (`koszulChangeOfBasis`), an isomorphism when `P` is
  (`koszulChangeOfBasisIso`); for an `r × r` matrix `P` this compares `K(f P; M)` with `K(f; M)`
  (`sequenceKoszulChangeOfBasis`, `sequenceKoszulChangeOfBasisIso`);
* base change along an algebra `A → B` (`koszulBaseChangeIso`, `sequenceKoszulBaseChangeIso`:
  `B ⊗_A K(f; M) ≅ K(f; B ⊗_A M)`), using that exterior powers of a free module commute with base
  change (`exteriorPowerBaseChangeEquiv`), and localization (`sequenceKoszulLocalizationIso`:
  `S⁻¹ K(f; M) ≅ K(f/1; S⁻¹ M)`).
-/

universe u

open ExteriorAlgebra TensorProduct CategoryTheory

namespace Hartshorne

namespace Koszul

variable {A : Type u} [CommRing A]

section Contraction

variable {V : Type*} [AddCommGroup V] [Module A V]

/-- Contraction by a linear form lowers the degree in the exterior algebra by one. -/
lemma contractLeft_mem_exteriorPower (φ : Module.Dual A V) (n : ℕ) {x : ExteriorAlgebra A V}
    (hx : x ∈ ⋀[A]^(n + 1) V) : CliffordAlgebra.contractLeft φ x ∈ ⋀[A]^n V := by
  induction n generalizing x with
  | zero =>
    rw [zero_add, exteriorPower, pow_one] at hx
    obtain ⟨v, rfl⟩ := hx
    rw [CliffordAlgebra.contractLeft_ι, exteriorPower, pow_zero]
    exact Submodule.algebraMap_mem _
  | succ n ih =>
    rw [exteriorPower, pow_succ'] at hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem a ha y hy =>
      obtain ⟨v, rfl⟩ := ha
      rw [CliffordAlgebra.contractLeft_ι_mul]
      refine sub_mem (Submodule.smul_mem _ _ hy) ?_
      rw [exteriorPower, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) (ih hy)
    | add a _ b _ ha hb => rw [map_add]; exact add_mem ha hb

/-- The contraction `⋀^{n+1} V → ⋀^n V` by a linear form `φ : V → A`. -/
noncomputable def contraction (φ : Module.Dual A V) (n : ℕ) :
    ⋀[A]^(n + 1) V →ₗ[A] ⋀[A]^n V :=
  ((CliffordAlgebra.contractLeft φ).comp (⋀[A]^(n + 1) V).subtype).codRestrict _
    fun x => contractLeft_mem_exteriorPower φ n x.2

@[simp]
lemma coe_contraction (φ : Module.Dual A V) (n : ℕ) (x : ⋀[A]^(n + 1) V) :
    (contraction φ n x : ExteriorAlgebra A V) = CliffordAlgebra.contractLeft φ x := rfl

/-- The contraction squares to zero. -/
@[simp]
lemma contraction_contraction (φ : Module.Dual A V) (n : ℕ) (x : ⋀[A]^(n + 2) V) :
    contraction φ n (contraction φ (n + 1) x) = 0 :=
  Subtype.ext (CliffordAlgebra.contractLeft_contractLeft _ _)

lemma contraction_comp_contraction (φ : Module.Dual A V) (n : ℕ) :
    contraction φ n ∘ₗ contraction φ (n + 1) = 0 :=
  LinearMap.ext (contraction_contraction φ n)

/-- The alternating formula for the contraction:
`d(v₀ ∧ ⋯ ∧ vₙ) = ∑ⱼ (-1)ʲ φ(vⱼ) v₀ ∧ ⋯ ∧ v̂ⱼ ∧ ⋯ ∧ vₙ`. -/
lemma contraction_ιMulti (φ : Module.Dual A V) (n : ℕ) (v : Fin (n + 1) → V) :
    contraction φ n (exteriorPower.ιMulti A (n + 1) v) =
      ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * φ (v j)) •
        exteriorPower.ιMulti A n (v ∘ j.succAbove) := by
  apply Subtype.ext
  simp only [coe_contraction, exteriorPower.ιMulti_apply_coe, Submodule.coe_sum,
    Submodule.coe_smul]
  induction n with
  | zero =>
    rw [ιMulti_succ_apply, ιMulti_zero_apply, mul_one, CliffordAlgebra.contractLeft_ι]
    simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    rw [ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul, ih, Fin.sum_univ_succ (n := n + 1)]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ, Finset.mul_sum,
      sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ιMulti_succ_apply, mul_smul_comm, ← neg_smul]
    congr 1
    · simp [Matrix.vecTail]
    · congr 2
      ext i
      simp [Matrix.vecTail, Fin.succ_succAbove_succ]

/-- In degree zero the contraction is evaluation of the linear form, under
`⋀^1 V ≅ V` and `⋀^0 V ≅ A`. -/
lemma zeroEquiv_contraction_zero (φ : Module.Dual A V) (x : ⋀[A]^1 V) :
    exteriorPower.zeroEquiv A V (contraction φ 0 x) = φ (exteriorPower.oneEquiv A V x) := by
  have : (exteriorPower.zeroEquiv A V).toLinearMap ∘ₗ contraction φ 0 =
      φ ∘ₗ (exteriorPower.oneEquiv A V).toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [contraction_ιMulti, exteriorPower.zeroEquiv_ιMulti, exteriorPower.oneEquiv_ιMulti]
  exact LinearMap.congr_fun this x

/-- The contraction is natural: for `P : W → V`, contracting by `φ` after `⋀ P` is `⋀ P` after
contracting by `φ ∘ P`. -/
lemma contraction_map {W : Type*} [AddCommGroup W] [Module A W] (P : W →ₗ[A] V)
    (φ : Module.Dual A V) (n : ℕ) (x : ⋀[A]^(n + 1) W) :
    contraction φ n (exteriorPower.map (n + 1) P x) =
      exteriorPower.map n P (contraction (φ ∘ₗ P) n x) := by
  have : contraction φ n ∘ₗ exteriorPower.map (n + 1) P =
      exteriorPower.map n P ∘ₗ contraction (φ ∘ₗ P) n := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [contraction_ιMulti, exteriorPower.map_apply_ιMulti, Function.comp_def]
  exact LinearMap.congr_fun this x

end Contraction

variable {V : Type u} [AddCommGroup V] [Module A V]

/-- Commutative squares of linear maps give commutative squares in `ModuleCat`. -/
lemma ofHom_comp_ofHom_eq {X Y Z T : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [AddCommGroup Z] [Module A Z] [AddCommGroup T] [Module A T]
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] T) (f' : X →ₗ[A] Z) (g' : Z →ₗ[A] T) (h : g ∘ₗ f = g' ∘ₗ f') :
    ModuleCat.ofHom f ≫ ModuleCat.ofHom g = ModuleCat.ofHom f' ≫ ModuleCat.ofHom g' := by
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, h]

section Complex

variable (φ : Module.Dual A V)

/-- The (homological) Koszul complex of a linear form `φ : V → A` with coefficients in `M`:
`K_p = ⋀^p V ⊗_A M`, with differential the contraction by `φ` tensored with `M`. For
`V = A^r` and `φ(eᵢ) = fᵢ` this is the Koszul complex `K_•(f₁, …, f_r; M)`. -/
noncomputable def koszulComplex (M : ModuleCat.{u} A) : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (⋀[A]^n V ⊗[A] M))
    (fun n => ModuleCat.ofHom ((contraction φ n).rTensor M))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, ← LinearMap.rTensor_comp, contraction_comp_contraction,
        LinearMap.rTensor_zero]
      rfl)

variable (M : ModuleCat.{u} A)

lemma koszulComplex_X (n : ℕ) :
    (koszulComplex φ M).X n = ModuleCat.of A (⋀[A]^n V ⊗[A] M) := rfl

@[simp]
lemma koszulComplex_d (n : ℕ) :
    (koszulComplex φ M).d (n + 1) n = ModuleCat.ofHom ((contraction φ n).rTensor M) := by
  simp [koszulComplex]

/-- The Koszul differential on decomposable tensors:
`d((v₀ ∧ ⋯ ∧ vₙ) ⊗ m) = ∑ⱼ (-1)ʲ (v₀ ∧ ⋯ ∧ v̂ⱼ ∧ ⋯ ∧ vₙ) ⊗ φ(vⱼ) m`. -/
lemma koszulComplex_d_tmul_ιMulti (n : ℕ) (v : Fin (n + 1) → V) (m : M) :
    ((koszulComplex φ M).d (n + 1) n).hom (exteriorPower.ιMulti A (n + 1) v ⊗ₜ[A] m) =
      ∑ j : Fin (n + 1), ((-1 : A) ^ (j : ℕ)) •
        (exteriorPower.ιMulti A n (v ∘ j.succAbove) ⊗ₜ[A] (φ (v j) • m)) := by
  rw [koszulComplex_d]
  change (contraction φ n).rTensor M (exteriorPower.ιMulti A (n + 1) v ⊗ₜ[A] m) = _
  rw [LinearMap.rTensor_tmul, contraction_ιMulti, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']

/-- The map of Koszul complexes induced by a linear map `g : M → N`. -/
noncomputable def koszulMap {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    koszulComplex φ M ⟶ koszulComplex φ N :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (g.hom.lTensor (⋀[A]^n V))) fun n => by
    simp only [koszulComplex_d]
    exact ofHom_comp_ofHom_eq _ _ _ _
      (by rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])

@[simp]
lemma koszulMap_f {M N : ModuleCat.{u} A} (g : M ⟶ N) (n : ℕ) :
    (koszulMap φ g).f n = ModuleCat.ofHom (g.hom.lTensor (⋀[A]^n V)) := rfl

/-- Functoriality of the Koszul complex in the coefficient module. -/
@[simps]
noncomputable def koszulFunctor : ModuleCat.{u} A ⥤ ChainComplex (ModuleCat.{u} A) ℕ where
  obj M := koszulComplex φ M
  map g := koszulMap φ g
  map_id M := by
    ext n : 2
    simp only [koszulMap_f, ModuleCat.hom_id, LinearMap.lTensor_id, HomologicalComplex.id_f]
    rfl
  map_comp f g := by
    ext n : 2
    simp only [koszulMap_f, ModuleCat.hom_comp, LinearMap.lTensor_comp, HomologicalComplex.comp_f]
    rfl

end Complex

section Augmentation

variable (φ : Module.Dual A V) (M : ModuleCat.{u} A)

/-- The submodule `I M ⊆ M`, where `I = φ(V)` is the ideal generated by the values of `φ`
(for `V = A^r`, `φ(eᵢ) = fᵢ`, this is `(f₁, …, f_r) M`). -/
abbrev koszulSubmodule (M : Type*) [AddCommGroup M] [Module A M] : Submodule A M :=
  (LinearMap.range φ : Ideal A) • ⊤

/-- The identification `K_0 = ⋀^0 V ⊗ M ≅ M`. -/
noncomputable def degreeZeroEquiv (M : Type*) [AddCommGroup M] [Module A M] :
    ⋀[A]^0 V ⊗[A] M ≃ₗ[A] M :=
  (LinearEquiv.rTensor M (exteriorPower.zeroEquiv A V)) ≪≫ₗ TensorProduct.lid A M

@[simp]
lemma degreeZeroEquiv_tmul {M : Type*} [AddCommGroup M] [Module A M] (x : ⋀[A]^0 V) (m : M) :
    degreeZeroEquiv (V := V) M (x ⊗ₜ m) = exteriorPower.zeroEquiv A V x • m := rfl

lemma degreeZeroEquiv_contraction_tmul {M : Type*} [AddCommGroup M] [Module A M]
    (x : ⋀[A]^1 V) (m : M) :
    degreeZeroEquiv M ((contraction φ 0).rTensor M (x ⊗ₜ m)) =
      φ (exteriorPower.oneEquiv A V x) • m := by
  simp [zeroEquiv_contraction_zero]

/-- The image of the first Koszul differential in `K_0 ≅ M` is `I M`. -/
lemma range_degreeZeroEquiv_comp_contraction (M : Type*) [AddCommGroup M] [Module A M] :
    LinearMap.range ((degreeZeroEquiv M).toLinearMap ∘ₗ (contraction φ 0).rTensor M) =
      koszulSubmodule φ M := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, degreeZeroEquiv_contraction_tmul]
      exact Submodule.smul_mem_smul (LinearMap.mem_range_self φ _) Submodule.mem_top
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · refine Submodule.smul_le.2 fun r hr m _ => ?_
    obtain ⟨v, rfl⟩ := hr
    refine ⟨(exteriorPower.oneEquiv A V).symm v ⊗ₜ m, ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, degreeZeroEquiv_contraction_tmul,
      LinearEquiv.apply_symm_apply]

/-- The augmentation `K_0 = ⋀^0 V ⊗ M ≅ M → M / I M`. -/
noncomputable def augmentationLinearMap (M : Type*) [AddCommGroup M] [Module A M] :
    ⋀[A]^0 V ⊗[A] M →ₗ[A] M ⧸ koszulSubmodule φ M :=
  (koszulSubmodule φ M).mkQ ∘ₗ (degreeZeroEquiv M).toLinearMap

lemma augmentationLinearMap_surjective (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Surjective (augmentationLinearMap φ M) :=
  (Submodule.mkQ_surjective _).comp (degreeZeroEquiv M).surjective

/-- Exactness of `K_1 → K_0 → M / I M → 0` at `K_0`. -/
lemma exact_contraction_augmentationLinearMap (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Exact ((contraction φ 0).rTensor M) (augmentationLinearMap φ M) := by
  intro x
  rw [augmentationLinearMap, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, ← range_degreeZeroEquiv_comp_contraction]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (degreeZeroEquiv M).injective hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

/-- The augmentation `K_0(φ; M) → M / I M` of the Koszul complex. -/
noncomputable def koszulAugmentation :
    (koszulComplex φ M).X 0 ⟶ ModuleCat.of A (M ⧸ koszulSubmodule φ M) :=
  ModuleCat.ofHom (augmentationLinearMap φ M)

@[simp]
lemma koszulAugmentation_tmul (x : ⋀[A]^0 V) (m : M) :
    (koszulAugmentation φ M).hom (x ⊗ₜ m) =
      Submodule.Quotient.mk (exteriorPower.zeroEquiv A V x • m) := rfl

@[reassoc (attr := simp)]
lemma koszulComplex_d_comp_koszulAugmentation :
    (koszulComplex φ M).d 1 0 ≫ koszulAugmentation φ M = 0 := by
  ext x
  exact (exact_contraction_augmentationLinearMap φ M).apply_apply_eq_zero x

/-- The augmentation identifies `M / I M` with the cokernel of `d₁ : K_1 → K_0`. -/
noncomputable def koszulAugmentationIsCokernel :
    Limits.IsColimit (Limits.CokernelCofork.ofπ (koszulAugmentation φ M)
      (koszulComplex_d_comp_koszulAugmentation φ M)) :=
  ModuleCat.isColimitCokernelCofork _ _ (by
      rw [show (koszulComplex φ M).d 1 0 = ModuleCat.ofHom ((contraction φ 0).rTensor M) from
        koszulComplex_d φ M 0]
      exact exact_contraction_augmentationLinearMap φ M)
    (augmentationLinearMap_surjective φ M)

/-- `H_0(K_•(φ; M)) ≅ M / I M`. -/
noncomputable def koszulHomologyZeroIso :
    (koszulComplex φ M).homology 0 ≅ ModuleCat.of A (M ⧸ koszulSubmodule φ M) :=
  (koszulComplex φ M).isoHomologyι₀ ≪≫
    Limits.IsColimit.coconePointUniqueUpToIso
      ((koszulComplex φ M).opcyclesIsCokernel 1 0 (by simp))
      (koszulAugmentationIsCokernel φ M)

/-- Under `H_0 ≅ M / I M`, the projection `K_0 → H_0` becomes the augmentation. -/
@[reassoc (attr := simp)]
lemma pOpcycles_isoHomologyι₀_inv_koszulHomologyZeroIso_hom :
    (koszulComplex φ M).pOpcycles 0 ≫ (koszulComplex φ M).isoHomologyι₀.inv ≫
      (koszulHomologyZeroIso φ M).hom = koszulAugmentation φ M := by
  simp only [koszulHomologyZeroIso, Iso.trans_hom, Iso.inv_hom_id_assoc]
  exact Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
    ((koszulComplex φ M).opcyclesIsCokernel 1 0 (by simp)) (koszulAugmentationIsCokernel φ M)
    Limits.WalkingParallelPair.one

/-- The map `M / I M → N / I N` induced by `g : M → N`. -/
noncomputable def koszulQuotientMap {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    ModuleCat.of A (M ⧸ koszulSubmodule φ M) ⟶ ModuleCat.of A (N ⧸ koszulSubmodule φ N) :=
  ModuleCat.ofHom (Submodule.mapQ _ _ g.hom (Submodule.smul_top_le_comap_smul_top _ _))

/-- The augmentation is natural in the coefficient module. -/
@[reassoc]
lemma koszulMap_f_zero_comp_koszulAugmentation {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    (koszulMap φ g).f 0 ≫ koszulAugmentation φ N =
      koszulAugmentation φ M ≫ koszulQuotientMap φ g := by
  ext1
  refine TensorProduct.ext' fun x m => ?_
  change augmentationLinearMap φ N (x ⊗ₜ g m) =
    Submodule.mapQ _ _ g.hom (Submodule.smul_top_le_comap_smul_top _ _)
      (augmentationLinearMap φ M (x ⊗ₜ m))
  simp [augmentationLinearMap]

end Augmentation

section ChangeOfBasis

variable {W : Type u} [AddCommGroup W] [Module A W]

/-- The change-of-basis map `⋀^• P ⊗ M : K_•(ψ; M) → K_•(φ; M)` attached to a linear map
`P : W → V` with `φ ∘ P = ψ`. -/
noncomputable def koszulChangeOfBasis (P : W →ₗ[A] V) {φ : Module.Dual A V}
    {ψ : Module.Dual A W} (h : φ ∘ₗ P = ψ) (M : ModuleCat.{u} A) :
    koszulComplex ψ M ⟶ koszulComplex φ M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom ((exteriorPower.map n P).rTensor M)) fun n => by
    subst h
    simp only [koszulComplex_d]
    exact ofHom_comp_ofHom_eq _ _ _ _ (by
      rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
      exact congrArg _ (LinearMap.ext fun x => contraction_map P φ n x))

@[simp]
lemma koszulChangeOfBasis_f (P : W →ₗ[A] V) {φ : Module.Dual A V} {ψ : Module.Dual A W}
    (h : φ ∘ₗ P = ψ) (M : ModuleCat.{u} A) (n : ℕ) :
    (koszulChangeOfBasis P h M).f n = ModuleCat.ofHom ((exteriorPower.map n P).rTensor M) := rfl

@[simp]
lemma koszulChangeOfBasis_id (φ : Module.Dual A V) (M : ModuleCat.{u} A) :
    koszulChangeOfBasis LinearMap.id (LinearMap.comp_id φ) M = 𝟙 (koszulComplex φ M) := by
  ext n : 2
  simp only [koszulChangeOfBasis_f, exteriorPower.map_id, LinearMap.rTensor_id,
    HomologicalComplex.id_f]
  rfl

lemma koszulChangeOfBasis_comp {U : Type u} [AddCommGroup U] [Module A U] (Q : U →ₗ[A] W)
    (P : W →ₗ[A] V) {φ : Module.Dual A V} {ψ : Module.Dual A W} {χ : Module.Dual A U}
    (h : φ ∘ₗ P = ψ) (h' : ψ ∘ₗ Q = χ) (M : ModuleCat.{u} A) :
    koszulChangeOfBasis Q h' M ≫ koszulChangeOfBasis P h M =
      koszulChangeOfBasis (P ∘ₗ Q) (by rw [← LinearMap.comp_assoc, h, h']) M := by
  ext n : 2
  simp only [HomologicalComplex.comp_f, koszulChangeOfBasis_f, exteriorPower.map_comp,
    LinearMap.rTensor_comp]
  rfl

/-- The change-of-basis maps commute with the functoriality in the coefficient module. -/
@[reassoc]
lemma koszulChangeOfBasis_naturality (P : W →ₗ[A] V) {φ : Module.Dual A V}
    {ψ : Module.Dual A W} (h : φ ∘ₗ P = ψ) {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    koszulMap ψ g ≫ koszulChangeOfBasis P h N = koszulChangeOfBasis P h M ≫ koszulMap φ g := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, koszulChangeOfBasis_f, koszulMap_f]
  exact ofHom_comp_ofHom_eq _ _ _ _
    (by rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])

/-- A linear isomorphism `P : W ≅ V` with `φ ∘ P = ψ` induces an isomorphism of Koszul
complexes `K_•(ψ; M) ≅ K_•(φ; M)`. -/
@[simps]
noncomputable def koszulChangeOfBasisIso (P : W ≃ₗ[A] V) {φ : Module.Dual A V}
    {ψ : Module.Dual A W} (h : φ ∘ₗ P.toLinearMap = ψ) (M : ModuleCat.{u} A) :
    koszulComplex ψ M ≅ koszulComplex φ M where
  hom := koszulChangeOfBasis P.toLinearMap h M
  inv := koszulChangeOfBasis P.symm.toLinearMap
    (LinearMap.ext fun v => by simp [← h]) M
  hom_inv_id := by
    rw [koszulChangeOfBasis_comp]
    convert koszulChangeOfBasis_id ψ M
    simp
  inv_hom_id := by
    rw [koszulChangeOfBasis_comp]
    convert koszulChangeOfBasis_id φ M
    simp

end ChangeOfBasis

section BaseChange

variable (B : Type u) [CommRing B] [Algebra A B]

/-- The base change `B ⊗_A K_•` of a chain complex of `A`-modules. -/
noncomputable def baseChangeComplex (K : ChainComplex (ModuleCat.{u} A) ℕ) :
    ChainComplex (ModuleCat.{u} B) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of B (B ⊗[A] K.X n))
    (fun n => ModuleCat.ofHom ((K.d (n + 1) n).hom.baseChange B))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp,
        K.d_comp_d, ModuleCat.hom_zero, LinearMap.baseChange_zero]
      rfl)

@[simp]
lemma baseChangeComplex_d (K : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (baseChangeComplex B K).d (n + 1) n =
      ModuleCat.ofHom ((K.d (n + 1) n).hom.baseChange B) := by
  simp [baseChangeComplex]

variable {B}

/-- The `A`-multilinear alternating map `(v₁, …, vₙ) ↦ (1 ⊗ v₁) ∧ ⋯ ∧ (1 ⊗ vₙ)`. -/
noncomputable def baseChangeAlternating (n : ℕ) :
    V [⋀^Fin n]→ₗ[A] ⋀[B]^n (B ⊗[A] V) :=
  { ((exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars A).compLinearMap
      (fun _ => TensorProduct.mk A B V 1) with
    map_eq_zero_of_eq' := fun v i j hv hij =>
      (exteriorPower.ιMulti B n).map_eq_zero_of_eq _ (by simp [hv]) hij }

@[simp]
lemma baseChangeAlternating_apply (n : ℕ) (v : Fin n → V) :
    baseChangeAlternating (B := B) n v = exteriorPower.ιMulti B n (fun i => (1 : B) ⊗ₜ[A] v i) :=
  rfl

/-- The canonical `B`-linear map `B ⊗_A ⋀^n_A V → ⋀^n_B (B ⊗_A V)`. -/
noncomputable def exteriorPowerBaseChange (n : ℕ) :
    B ⊗[A] ⋀[A]^n V →ₗ[B] ⋀[B]^n (B ⊗[A] V) :=
  LinearMap.liftBaseChange B (exteriorPower.alternatingMapLinearEquiv (baseChangeAlternating n))

@[simp]
lemma exteriorPowerBaseChange_tmul_ιMulti (n : ℕ) (b : B) (v : Fin n → V) :
    exteriorPowerBaseChange n (b ⊗ₜ exteriorPower.ιMulti A n v) =
      b • exteriorPower.ιMulti B n (fun i => (1 : B) ⊗ₜ[A] v i) := by
  simp [exteriorPowerBaseChange, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- For `V` with a basis, `B ⊗_A ⋀^n_A V → ⋀^n_B (B ⊗_A V)` is bijective. -/
lemma exteriorPowerBaseChange_bijective {I : Type*} [LinearOrder I] (b : Module.Basis I A V)
    (n : ℕ) : Function.Bijective (exteriorPowerBaseChange (A := A) (B := B) (V := V) n) := by
  let e := ((b.exteriorPower n).baseChange B).equiv ((b.baseChange B).exteriorPower n)
    (Equiv.refl _)
  have : exteriorPowerBaseChange n = e.toLinearMap := by
    refine ((b.exteriorPower n).baseChange B).ext fun s => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply,
      Module.Basis.baseChange_apply, exteriorPower.basis_apply, exteriorPower.basis_apply]
    simp [exteriorPower.ιMulti_family, Function.comp_def, Module.Basis.baseChange_apply]
  rw [this]
  exact e.bijective

/-- For a free module `V`, exterior powers commute with base change:
`B ⊗_A ⋀^n_A V ≅ ⋀^n_B (B ⊗_A V)`. -/
noncomputable def exteriorPowerBaseChangeEquiv [Module.Free A V] (n : ℕ) :
    B ⊗[A] ⋀[A]^n V ≃ₗ[B] ⋀[B]^n (B ⊗[A] V) :=
  LinearEquiv.ofBijective (exteriorPowerBaseChange n) (by
    let : LinearOrder (Module.Free.ChooseBasisIndex A V) :=
      IsWellOrder.linearOrder WellOrderingRel
    exact exteriorPowerBaseChange_bijective (Module.Free.chooseBasis A V) n)

@[simp]
lemma exteriorPowerBaseChangeEquiv_apply [Module.Free A V] (n : ℕ) (x : B ⊗[A] ⋀[A]^n V) :
    exteriorPowerBaseChangeEquiv n x = exteriorPowerBaseChange n x := rfl

/-- The contraction commutes with base change. -/
lemma contraction_exteriorPowerBaseChange (φ : Module.Dual A V) (n : ℕ)
    (x : B ⊗[A] ⋀[A]^(n + 1) V) :
    contraction (φ.baseChange B) n (exteriorPowerBaseChange (n + 1) x) =
      exteriorPowerBaseChange n ((contraction φ n).baseChange B x) := by
  have key : ∀ y : ⋀[A]^(n + 1) V,
      contraction (φ.baseChange B) n (exteriorPowerBaseChange (n + 1) ((1 : B) ⊗ₜ y)) =
        exteriorPowerBaseChange n ((1 : B) ⊗ₜ contraction φ n y) := by
    intro y
    have : ((contraction (φ.baseChange B) n).restrictScalars A ∘ₗ
          (exteriorPowerBaseChange (n + 1)).restrictScalars A ∘ₗ
            TensorProduct.mk A B (⋀[A]^(n + 1) V) 1) =
        (exteriorPowerBaseChange n).restrictScalars A ∘ₗ
          TensorProduct.mk A B (⋀[A]^n V) 1 ∘ₗ contraction φ n := by
      apply exteriorPower.linearMap_ext
      ext v
      simp [contraction_ιMulti, TensorProduct.tmul_sum, Algebra.smul_def, Function.comp_def,
        ← IsScalarTower.algebraMap_apply]
    exact LinearMap.congr_fun this y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y =>
    rw [show b ⊗ₜ[A] y = b • ((1 : B) ⊗ₜ[A] y) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    simp only [map_smul, key, LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The degreewise isomorphism `B ⊗_A (⋀^n V ⊗_A M) ≅ ⋀^n_B (B ⊗_A V) ⊗_B (B ⊗_A M)`. -/
noncomputable def koszulBaseChangeTermEquiv [Module.Free A V] (M : Type u) [AddCommGroup M]
    [Module A M] (n : ℕ) :
    B ⊗[A] (⋀[A]^n V ⊗[A] M) ≃ₗ[B] ⋀[B]^n (B ⊗[A] V) ⊗[B] (B ⊗[A] M) :=
  TensorProduct.AlgebraTensorModule.distribBaseChange A B (⋀[A]^n V) M ≪≫ₗ
    LinearEquiv.rTensor (B ⊗[A] M) (exteriorPowerBaseChangeEquiv n)

@[simp]
lemma koszulBaseChangeTermEquiv_tmul [Module.Free A V] (M : Type u) [AddCommGroup M]
    [Module A M] (n : ℕ) (b : B) (y : ⋀[A]^n V) (m : M) :
    koszulBaseChangeTermEquiv M n (b ⊗ₜ (y ⊗ₜ m)) =
      exteriorPowerBaseChange n (b ⊗ₜ y) ⊗ₜ ((1 : B) ⊗ₜ m) := rfl

/-- The degreewise isomorphisms commute with the Koszul differentials. -/
lemma koszulBaseChangeTermEquiv_comm [Module.Free A V] (φ : Module.Dual A V) (M : Type u)
    [AddCommGroup M] [Module A M] (n : ℕ) :
    (contraction (φ.baseChange B) n).rTensor (B ⊗[A] M) ∘ₗ
        (koszulBaseChangeTermEquiv M (n + 1)).toLinearMap =
      (koszulBaseChangeTermEquiv M n).toLinearMap ∘ₗ ((contraction φ n).rTensor M).baseChange B := by
  refine TensorProduct.AlgebraTensorModule.ext fun b z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y m =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, koszulBaseChangeTermEquiv_tmul,
      LinearMap.rTensor_tmul, contraction_exteriorPowerBaseChange, LinearMap.baseChange_tmul]
  | add y z hy hz =>
    simp only [LinearMap.comp_apply, TensorProduct.tmul_add, map_add] at hy hz ⊢
    rw [hy, hz]

/-- Compatibility of the Koszul complex with base change: for a free module `V`,
`B ⊗_A K_•(φ; M) ≅ K_•(φ_B; B ⊗_A M)` as complexes of `B`-modules. -/
noncomputable def koszulBaseChangeIso [Module.Free A V] (φ : Module.Dual A V)
    (M : ModuleCat.{u} A) :
    baseChangeComplex B (koszulComplex φ M) ≅
      koszulComplex (φ.baseChange B) (ModuleCat.of B (B ⊗[A] M)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (koszulBaseChangeTermEquiv (B := B) (V := V) M n).toModuleIso) (by
      rintro i n (rfl : n + 1 = i)
      rw [baseChangeComplex_d, koszulComplex_d, koszulComplex_d]
      exact ofHom_comp_ofHom_eq _ _ _ _ (koszulBaseChangeTermEquiv_comm φ M n))

end BaseChange

section Sequence

variable {r : ℕ} (f : Fin r → A)

/-- The linear form `A^r → A`, `eᵢ ↦ fᵢ`, attached to a sequence `f₁, …, f_r`. -/
noncomputable def koszulForm : Module.Dual A (Fin r → A) :=
  Fintype.linearCombination A f

lemma koszulForm_apply (v : Fin r → A) : koszulForm f v = ∑ i, v i * f i := by
  simp [koszulForm, Fintype.linearCombination_apply]

@[simp]
lemma koszulForm_single (i : Fin r) : koszulForm f (Pi.single i 1) = f i := by
  simp [koszulForm_apply, Pi.single_apply]

/-- The values of `eᵢ ↦ fᵢ` form the ideal `(f₁, …, f_r)`. -/
lemma range_koszulForm : LinearMap.range (koszulForm f) = Ideal.span (Set.range f) :=
  Fintype.range_linearCombination A f

/-- The Koszul complex `K_•(f₁, …, f_r; M)`, with `K_p = ⋀^p (A^r) ⊗_A M`. -/
noncomputable abbrev sequenceKoszulComplex (M : ModuleCat.{u} A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  koszulComplex (koszulForm f) M

/-- The Koszul differential in the standard basis:
`d(e_{i₀} ∧ ⋯ ∧ e_{iₚ} ⊗ m) = ∑ⱼ (-1)ʲ e_{i₀} ∧ ⋯ ∧ ê_{iⱼ} ∧ ⋯ ∧ e_{iₚ} ⊗ f_{iⱼ} m`. -/
lemma sequenceKoszulComplex_d_basis (M : ModuleCat.{u} A) (n : ℕ) (i : Fin (n + 1) → Fin r)
    (m : M) :
    ((sequenceKoszulComplex f M).d (n + 1) n).hom
        (exteriorPower.ιMulti A (n + 1) (fun k => Pi.single (i k) 1) ⊗ₜ[A] m) =
      ∑ j : Fin (n + 1), ((-1 : A) ^ (j : ℕ)) •
        (exteriorPower.ιMulti A n (fun k => Pi.single (i (j.succAbove k)) 1) ⊗ₜ[A]
          (f (i j) • m)) := by
  rw [koszulComplex_d_tmul_ιMulti]
  simp only [Function.comp_def, koszulForm_single]
  rfl

/-- `H_0(K_•(f; M)) ≅ M / (f₁, …, f_r) M`. -/
noncomputable def sequenceKoszulHomologyZeroIso (M : ModuleCat.{u} A) :
    (sequenceKoszulComplex f M).homology 0 ≅
      ModuleCat.of A (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule A M)) :=
  koszulHomologyZeroIso (koszulForm f) M ≪≫
    (Submodule.quotEquivOfEq _ _ (by rw [koszulSubmodule, range_koszulForm])).toModuleIso

/-- For a matrix `P`, the form of `f` composed with `P` is the form of the sequence `f P`. -/
lemma koszulForm_comp_toLin' (P : Matrix (Fin r) (Fin r) A) :
    koszulForm f ∘ₗ Matrix.toLin' P = koszulForm (Matrix.vecMul f P) := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply, koszulForm_apply]
  change dotProduct (Matrix.mulVec P v) f = dotProduct v (Matrix.vecMul f P)
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

/-- The change-of-basis map `K_•(f P; M) → K_•(f; M)` attached to an `r × r` matrix `P`. -/
noncomputable def sequenceKoszulChangeOfBasis (P : Matrix (Fin r) (Fin r) A)
    (M : ModuleCat.{u} A) :
    sequenceKoszulComplex (Matrix.vecMul f P) M ⟶ sequenceKoszulComplex f M :=
  koszulChangeOfBasis (Matrix.toLin' P) (koszulForm_comp_toLin' f P) M

/-- For an invertible matrix `P`, the change-of-basis map is an isomorphism
`K_•(f P; M) ≅ K_•(f; M)`. -/
noncomputable def sequenceKoszulChangeOfBasisIso (P : Matrix (Fin r) (Fin r) A)
    [Invertible P] (M : ModuleCat.{u} A) :
    sequenceKoszulComplex (Matrix.vecMul f P) M ≅ sequenceKoszulComplex f M :=
  koszulChangeOfBasisIso (Matrix.toLinearEquiv' P inferInstance)
    (koszulForm_comp_toLin' f P) M

@[simp]
lemma sequenceKoszulChangeOfBasisIso_hom (P : Matrix (Fin r) (Fin r) A) [Invertible P]
    (M : ModuleCat.{u} A) :
    (sequenceKoszulChangeOfBasisIso f P M).hom = sequenceKoszulChangeOfBasis f P M := rfl

variable (B : Type u) [CommRing B] [Algebra A B]

/-- Base change of the sequence form, identified with the form of `φ(f₁), …, φ(f_r)` on `B^r`. -/
lemma koszulForm_comp_piScalarRight :
    koszulForm (fun i => algebraMap A B (f i)) ∘ₗ
        (TensorProduct.piScalarRight A B B (Fin r)).toLinearMap =
      (koszulForm f).baseChange B := by
  ext v
  simp [koszulForm_apply, Algebra.smul_def, Finset.mul_sum, mul_comm]

/-- Compatibility with base change along `A → B`:
`B ⊗_A K_•(f; M) ≅ K_•(φ(f₁), …, φ(f_r); B ⊗_A M)`. -/
noncomputable def sequenceKoszulBaseChangeIso (M : ModuleCat.{u} A) :
    baseChangeComplex B (sequenceKoszulComplex f M) ≅
      sequenceKoszulComplex (fun i => algebraMap A B (f i)) (ModuleCat.of B (B ⊗[A] M)) :=
  koszulBaseChangeIso (koszulForm f) M ≪≫
    koszulChangeOfBasisIso (TensorProduct.piScalarRight A B B (Fin r))
      (koszulForm_comp_piScalarRight f B) _

/-- Compatibility with localization: for a multiplicative set `S ⊆ A`,
`S⁻¹ K_•(f; M) ≅ K_•(f₁/1, …, f_r/1; S⁻¹ M)` as complexes of `S⁻¹ A`-modules. -/
noncomputable def sequenceKoszulLocalizationIso (S : Submonoid A) (M : ModuleCat.{u} A) :
    baseChangeComplex (Localization S) (sequenceKoszulComplex f M) ≅
      sequenceKoszulComplex (fun i => algebraMap A (Localization S) (f i))
        (ModuleCat.of (Localization S) (LocalizedModule S M)) :=
  sequenceKoszulBaseChangeIso f (Localization S) M ≪≫
    (koszulFunctor _).mapIso
      (IsLocalizedModule.isBaseChange S (Localization S)
        (LocalizedModule.mkLinearMap S M)).equiv.toModuleIso

end Sequence

end Koszul

end Hartshorne
