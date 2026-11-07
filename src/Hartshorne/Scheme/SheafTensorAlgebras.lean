/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Hartshorne.Scheme.SheafAlgebraOperations

/-!
# Tensor, symmetric and exterior algebras of module sheaves

Hartshorne, *Algebraic Geometry*, II, Exercise 5.16 (printed p. 127).

Let `(X, 𝒪_X)` be a ringed space and `F` an `𝒪_X`-module. Following Hartshorne, the tensor
algebra `T(F)` is the sheaf associated to the presheaf `U ↦ T(F(U))` of `𝒪_X`-algebras
(`moduleSheafTensorAlgebra`, with its sheaf of `𝒪_X`-algebras structure
`moduleSheafTensorAlgebraStructure`). Its homogeneous components are the tensor powers: the maps
`T^r F → T(F)` (`moduleSheafTensorAlgebraι`) exhibit `T(F)` as the direct sum of the `T^r F`
(`moduleSheafTensorAlgebra_isColimit`), and multiplication maps `T^r F × T^s F` to `T^{r+s} F`
(`moduleSheafTensorAlgebra_mul_ι`).
-/

universe u

open CategoryTheory MonoidalCategory TopologicalSpace Opposite Limits
open scoped TensorProduct DirectSum

namespace Hartshorne

namespace SheafTensorOperations

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module B N] [Module C P]

/-- The multiplication of an `A`-algebra, as an `A`-bilinear map. -/
noncomputable def algebraMulBilinear (A' : Type u) [CommRing A'] (T : Type u) [Ring T]
    [Algebra A' T] : T →ₗ[A'] T →ₗ[A'] T :=
  LinearMap.mk₂ A' (· * ·) add_mul (fun c a b => Algebra.smul_mul_assoc c a b) mul_add
    (fun c a b => Algebra.mul_smul_comm c a b)

@[simp]
lemma algebraMulBilinear_apply (A' : Type u) [CommRing A'] {T : Type u} [Ring T] [Algebra A' T]
    (a b : T) : algebraMulBilinear A' T a b = a * b := rfl

section TensorAlgebra

/-- The ring homomorphism `T_A(M) → T_B(N)` induced by a `σ`-semilinear map `M → N`. -/
noncomputable def tensorAlgebraRingHom (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    TensorAlgebra A M →+* TensorAlgebra B N :=
  letI : Algebra A (TensorAlgebra B N) := ((algebraMap B (TensorAlgebra B N)).comp σ).toAlgebra'
    (fun c x => Algebra.commutes (σ c) x)
  (TensorAlgebra.lift A
    { toFun := fun m => TensorAlgebra.ι B (f m)
      map_add' := fun m m' => by rw [map_add, map_add]
      map_smul' := fun a m => by
        rw [map_smulₛₗ, map_smul, RingHom.id_apply]
        exact (Algebra.smul_def (σ a) _).trans (Algebra.smul_def a _).symm }).toRingHom

@[simp]
lemma tensorAlgebraRingHom_ι (σ : A →+* B) (f : M →ₛₗ[σ] N) (m : M) :
    tensorAlgebraRingHom σ f (TensorAlgebra.ι A m) = TensorAlgebra.ι B (f m) := by
  let : Algebra A (TensorAlgebra B N) := ((algebraMap B (TensorAlgebra B N)).comp σ).toAlgebra'
    (fun c x => Algebra.commutes (σ c) x)
  exact TensorAlgebra.lift_ι_apply _ m

@[simp]
lemma tensorAlgebraRingHom_algebraMap (σ : A →+* B) (f : M →ₛₗ[σ] N) (a : A) :
    tensorAlgebraRingHom σ f (algebraMap A (TensorAlgebra A M) a) =
      algebraMap B (TensorAlgebra B N) (σ a) := by
  let : Algebra A (TensorAlgebra B N) := ((algebraMap B (TensorAlgebra B N)).comp σ).toAlgebra'
    (fun c x => Algebra.commutes (σ c) x)
  exact AlgHom.commutes _ a

/-- The `σ`-semilinear map `T_A(M) → T_B(N)` induced by a `σ`-semilinear map `M → N`. -/
noncomputable def tensorAlgebraMap (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    TensorAlgebra A M →ₛₗ[σ] TensorAlgebra B N where
  toFun := tensorAlgebraRingHom σ f
  map_add' := map_add _
  map_smul' a x := by
    rw [Algebra.smul_def, map_mul, tensorAlgebraRingHom_algebraMap, ← Algebra.smul_def]

lemma tensorAlgebraMap_apply (σ : A →+* B) (f : M →ₛₗ[σ] N) (x : TensorAlgebra A M) :
    tensorAlgebraMap σ f x = tensorAlgebraRingHom σ f x := rfl

theorem tensorAlgebraMap_mul (σ : A →+* B) (f : M →ₛₗ[σ] N) (a b : TensorAlgebra A M) :
    tensorAlgebraMap σ f (algebraMulBilinear A _ a b) =
      algebraMulBilinear B _ (tensorAlgebraMap σ f a) (tensorAlgebraMap σ f b) :=
  map_mul (tensorAlgebraRingHom σ f) a b

theorem tensorAlgebraMap_id {σ : A →+* A} (hσ : ∀ a, σ a = a) (f : M →ₛₗ[σ] M)
    (hf : ∀ m, f m = m) (x : TensorAlgebra A M) : tensorAlgebraMap σ f x = x := by
  rw [tensorAlgebraMap_apply]
  induction x using TensorAlgebra.induction with
  | algebraMap a => rw [tensorAlgebraRingHom_algebraMap, hσ]
  | ι m => rw [tensorAlgebraRingHom_ι, hf]
  | mul a b ha hb => rw [map_mul, ha, hb]
  | add a b ha hb => rw [map_add, ha, hb]

theorem tensorAlgebraMap_comp {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
    (hρ : ∀ a, ρ a = τ (σ a)) (f : M →ₛₗ[σ] N) (g : N →ₛₗ[τ] P) (h : M →ₛₗ[ρ] P)
    (hh : ∀ m, h m = g (f m)) (x : TensorAlgebra A M) :
    tensorAlgebraMap ρ h x = tensorAlgebraMap τ g (tensorAlgebraMap σ f x) := by
  simp only [tensorAlgebraMap_apply]
  induction x using TensorAlgebra.induction with
  | algebraMap a => rw [tensorAlgebraRingHom_algebraMap, tensorAlgebraRingHom_algebraMap,
      tensorAlgebraRingHom_algebraMap, hρ]
  | ι m => rw [tensorAlgebraRingHom_ι, tensorAlgebraRingHom_ι, tensorAlgebraRingHom_ι, hh]
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]

theorem tensorAlgebraMap_toTensorAlgebra (r : ℕ) (σ : A →+* B) (f : M →ₛₗ[σ] N)
    (x : ⨂[A]^r M) :
    tensorAlgebraMap σ f (TensorPower.toTensorAlgebra x) =
      TensorPower.toTensorAlgebra (tensorPowerMap r σ f x) := by
  have hx : x ∈ Submodule.span A (Set.range (PiTensorProduct.tprod A)) :=
    PiTensorProduct.span_tprod_eq_top (R := A) (s := fun _ : Fin r => M) ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    rw [TensorPower.toTensorAlgebra_tprod, tensorPowerMap_tprod, TensorPower.toTensorAlgebra_tprod,
      TensorAlgebra.tprod_apply, TensorAlgebra.tprod_apply, tensorAlgebraMap_apply, map_list_prod,
      List.map_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => tensorAlgebraRingHom_ι σ f (m i))
  | zero => simp only [map_zero]
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul a y _ hy => simp only [map_smul, map_smulₛₗ, hy]

theorem toTensorAlgebra_directSum_bijective :
    Function.Bijective (DirectSum.toModule A ℕ (TensorAlgebra A M)
      (fun r => (TensorPower.toTensorAlgebra : ⨂[A]^r M →ₗ[A] TensorAlgebra A M))) := by
  change Function.Bijective (TensorAlgebra.ofDirectSum (R := A) (M := M))
  exact Function.bijective_iff_has_inverse.2 ⟨TensorAlgebra.toDirectSum,
    TensorAlgebra.toDirectSum_ofDirectSum, TensorAlgebra.ofDirectSum_toDirectSum⟩

theorem toTensorAlgebra_mul_mem (r s : ℕ) (a : ⨂[A]^r M) (b : ⨂[A]^s M) :
    TensorPower.toTensorAlgebra a * TensorPower.toTensorAlgebra b ∈
      LinearMap.range (TensorPower.toTensorAlgebra : ⨂[A]^(r + s) M →ₗ[A] TensorAlgebra A M) :=
  ⟨_, TensorPower.toTensorAlgebra_gMul a b⟩

end TensorAlgebra

section ExteriorAlgebra

/-- The ring homomorphism `⋀_A(M) → ⋀_B(N)` induced by a `σ`-semilinear map `M → N`. -/
noncomputable def exteriorAlgebraRingHom (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    ExteriorAlgebra A M →+* ExteriorAlgebra B N :=
  letI : Algebra A (ExteriorAlgebra B N) :=
    ((algebraMap B (ExteriorAlgebra B N)).comp σ).toAlgebra' (fun c x => Algebra.commutes (σ c) x)
  (ExteriorAlgebra.lift A ⟨
    { toFun := fun m => ExteriorAlgebra.ι B (f m)
      map_add' := fun m m' => by rw [map_add, map_add]
      map_smul' := fun a m => by
        rw [map_smulₛₗ, map_smul, RingHom.id_apply]
        exact (Algebra.smul_def (σ a) _).trans (Algebra.smul_def a _).symm },
    fun m => ExteriorAlgebra.ι_sq_zero (f m)⟩).toRingHom

@[simp]
lemma exteriorAlgebraRingHom_ι (σ : A →+* B) (f : M →ₛₗ[σ] N) (m : M) :
    exteriorAlgebraRingHom σ f (ExteriorAlgebra.ι A m) = ExteriorAlgebra.ι B (f m) := by
  let _ : Algebra A (ExteriorAlgebra B N) :=
    ((algebraMap B (ExteriorAlgebra B N)).comp σ).toAlgebra' (fun c x => Algebra.commutes (σ c) x)
  exact ExteriorAlgebra.lift_ι_apply _ _ _ m

@[simp]
lemma exteriorAlgebraRingHom_algebraMap (σ : A →+* B) (f : M →ₛₗ[σ] N) (a : A) :
    exteriorAlgebraRingHom σ f (algebraMap A (ExteriorAlgebra A M) a) =
      algebraMap B (ExteriorAlgebra B N) (σ a) := by
  let _ : Algebra A (ExteriorAlgebra B N) :=
    ((algebraMap B (ExteriorAlgebra B N)).comp σ).toAlgebra' (fun c x => Algebra.commutes (σ c) x)
  exact AlgHom.commutes _ a

/-- The `σ`-semilinear map `⋀_A(M) → ⋀_B(N)` induced by a `σ`-semilinear map `M → N`. -/
noncomputable def exteriorAlgebraMap (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    ExteriorAlgebra A M →ₛₗ[σ] ExteriorAlgebra B N where
  toFun := exteriorAlgebraRingHom σ f
  map_add' := map_add _
  map_smul' a x := by
    rw [Algebra.smul_def, map_mul, exteriorAlgebraRingHom_algebraMap, ← Algebra.smul_def]

lemma exteriorAlgebraMap_apply (σ : A →+* B) (f : M →ₛₗ[σ] N) (x : ExteriorAlgebra A M) :
    exteriorAlgebraMap σ f x = exteriorAlgebraRingHom σ f x := rfl

theorem exteriorAlgebraMap_mul (σ : A →+* B) (f : M →ₛₗ[σ] N) (a b : ExteriorAlgebra A M) :
    exteriorAlgebraMap σ f (algebraMulBilinear A _ a b) =
      algebraMulBilinear B _ (exteriorAlgebraMap σ f a) (exteriorAlgebraMap σ f b) :=
  map_mul (exteriorAlgebraRingHom σ f) a b

theorem exteriorAlgebraMap_id {σ : A →+* A} (hσ : ∀ a, σ a = a) (f : M →ₛₗ[σ] M)
    (hf : ∀ m, f m = m) (x : ExteriorAlgebra A M) : exteriorAlgebraMap σ f x = x := by
  rw [exteriorAlgebraMap_apply]
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => rw [exteriorAlgebraRingHom_algebraMap, hσ]
  | ι m => rw [exteriorAlgebraRingHom_ι, hf]
  | mul a b ha hb => rw [map_mul, ha, hb]
  | add a b ha hb => rw [map_add, ha, hb]

theorem exteriorAlgebraMap_comp {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
    (hρ : ∀ a, ρ a = τ (σ a)) (f : M →ₛₗ[σ] N) (g : N →ₛₗ[τ] P) (h : M →ₛₗ[ρ] P)
    (hh : ∀ m, h m = g (f m)) (x : ExteriorAlgebra A M) :
    exteriorAlgebraMap ρ h x = exteriorAlgebraMap τ g (exteriorAlgebraMap σ f x) := by
  simp only [exteriorAlgebraMap_apply]
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => rw [exteriorAlgebraRingHom_algebraMap, exteriorAlgebraRingHom_algebraMap,
      exteriorAlgebraRingHom_algebraMap, hρ]
  | ι m => rw [exteriorAlgebraRingHom_ι, exteriorAlgebraRingHom_ι, exteriorAlgebraRingHom_ι, hh]
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]

theorem exteriorAlgebraMap_coe (r : ℕ) (σ : A →+* B) (f : M →ₛₗ[σ] N) (x : ⋀[A]^r M) :
    exteriorAlgebraMap σ f (x : ExteriorAlgebra A M) = (exteriorPowerMap r σ f x : ExteriorAlgebra B N) := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A r)) :=
    exteriorPower.ιMulti_span A r M ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    rw [exteriorPowerMap_ιMulti, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, exteriorAlgebraMap_apply,
      map_list_prod, List.map_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => exteriorAlgebraRingHom_ι σ f (m i))
  | zero => simp only [ZeroMemClass.coe_zero, map_zero]
  | add y z _ _ hy hz => simp only [Submodule.coe_add, map_add, hy, hz]
  | smul a y _ hy => simp only [Submodule.coe_smul, map_smulₛₗ, hy]

theorem exteriorPower_directSum_bijective :
    Function.Bijective (DirectSum.toModule A ℕ (ExteriorAlgebra A M)
      (fun r => (⋀[A]^r M).subtype)) :=
  DirectSum.Decomposition.isInternal (fun r : ℕ => ⋀[A]^r M)

theorem exteriorPower_mul_mem (r s : ℕ) (a : ⋀[A]^r M) (b : ⋀[A]^s M) :
    (a : ExteriorAlgebra A M) * b ∈ LinearMap.range (⋀[A]^(r + s) M).subtype := by
  rw [Submodule.range_subtype]
  exact SetLike.mul_mem_graded a.2 b.2

end ExteriorAlgebra

section SymmetricAlgebra

/-- The ring homomorphism `S_A(M) → S_B(N)` induced by a `σ`-semilinear map `M → N`. -/
noncomputable def symmetricAlgebraRingHom (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    SymmetricAlgebra A M →+* SymmetricAlgebra B N :=
  letI : Algebra A (SymmetricAlgebra B N) :=
    ((algebraMap B (SymmetricAlgebra B N)).comp σ).toAlgebra
  (SymmetricAlgebra.lift
    { toFun := fun m => SymmetricAlgebra.ι B N (f m)
      map_add' := fun m m' => by rw [map_add, map_add]
      map_smul' := fun a m => by
        rw [map_smulₛₗ, map_smul, RingHom.id_apply]
        exact (Algebra.smul_def (σ a) _).trans (Algebra.smul_def a _).symm }).toRingHom

@[simp]
lemma symmetricAlgebraRingHom_ι (σ : A →+* B) (f : M →ₛₗ[σ] N) (m : M) :
    symmetricAlgebraRingHom σ f (SymmetricAlgebra.ι A M m) = SymmetricAlgebra.ι B N (f m) := by
  let _ : Algebra A (SymmetricAlgebra B N) :=
    ((algebraMap B (SymmetricAlgebra B N)).comp σ).toAlgebra
  exact SymmetricAlgebra.lift_ι_apply _ m

@[simp]
lemma symmetricAlgebraRingHom_algebraMap (σ : A →+* B) (f : M →ₛₗ[σ] N) (a : A) :
    symmetricAlgebraRingHom σ f (algebraMap A (SymmetricAlgebra A M) a) =
      algebraMap B (SymmetricAlgebra B N) (σ a) := by
  let _ : Algebra A (SymmetricAlgebra B N) :=
    ((algebraMap B (SymmetricAlgebra B N)).comp σ).toAlgebra
  exact AlgHom.commutes _ a

lemma symmetricAlgebraRingHom_algHom (σ : A →+* B) (f : M →ₛₗ[σ] N) (t : TensorAlgebra A M) :
    symmetricAlgebraRingHom σ f (SymmetricAlgebra.algHom A M t) =
      SymmetricAlgebra.algHom B N (tensorAlgebraRingHom σ f t) := by
  induction t using TensorAlgebra.induction with
  | algebraMap a => rw [AlgHom.commutes, symmetricAlgebraRingHom_algebraMap,
      tensorAlgebraRingHom_algebraMap, AlgHom.commutes]
  | ι m =>
    rw [tensorAlgebraRingHom_ι]
    exact symmetricAlgebraRingHom_ι σ f m
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- The `σ`-semilinear map `S_A(M) → S_B(N)` induced by a `σ`-semilinear map `M → N`. -/
noncomputable def symmetricAlgebraMap (σ : A →+* B) (f : M →ₛₗ[σ] N) :
    SymmetricAlgebra A M →ₛₗ[σ] SymmetricAlgebra B N where
  toFun := symmetricAlgebraRingHom σ f
  map_add' := map_add _
  map_smul' a x := by
    rw [Algebra.smul_def, map_mul, symmetricAlgebraRingHom_algebraMap, ← Algebra.smul_def]

lemma symmetricAlgebraMap_apply (σ : A →+* B) (f : M →ₛₗ[σ] N) (x : SymmetricAlgebra A M) :
    symmetricAlgebraMap σ f x = symmetricAlgebraRingHom σ f x := rfl

theorem symmetricAlgebraMap_mul (σ : A →+* B) (f : M →ₛₗ[σ] N) (a b : SymmetricAlgebra A M) :
    symmetricAlgebraMap σ f (algebraMulBilinear A _ a b) =
      algebraMulBilinear B _ (symmetricAlgebraMap σ f a) (symmetricAlgebraMap σ f b) :=
  map_mul (symmetricAlgebraRingHom σ f) a b

theorem symmetricAlgebraMap_id {σ : A →+* A} (hσ : ∀ a, σ a = a) (f : M →ₛₗ[σ] M)
    (hf : ∀ m, f m = m) (x : SymmetricAlgebra A M) : symmetricAlgebraMap σ f x = x := by
  rw [symmetricAlgebraMap_apply]
  induction x using SymmetricAlgebra.induction with
  | algebraMap a => rw [symmetricAlgebraRingHom_algebraMap, hσ]
  | ι m => rw [symmetricAlgebraRingHom_ι, hf]
  | mul a b ha hb => rw [map_mul, ha, hb]
  | add a b ha hb => rw [map_add, ha, hb]

theorem symmetricAlgebraMap_comp {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
    (hρ : ∀ a, ρ a = τ (σ a)) (f : M →ₛₗ[σ] N) (g : N →ₛₗ[τ] P) (h : M →ₛₗ[ρ] P)
    (hh : ∀ m, h m = g (f m)) (x : SymmetricAlgebra A M) :
    symmetricAlgebraMap ρ h x = symmetricAlgebraMap τ g (symmetricAlgebraMap σ f x) := by
  simp only [symmetricAlgebraMap_apply]
  induction x using SymmetricAlgebra.induction with
  | algebraMap a => rw [symmetricAlgebraRingHom_algebraMap, symmetricAlgebraRingHom_algebraMap,
      symmetricAlgebraRingHom_algebraMap, hρ]
  | ι m => rw [symmetricAlgebraRingHom_ι, symmetricAlgebraRingHom_ι, symmetricAlgebraRingHom_ι, hh]
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]

variable (r : ℕ)

theorem symmetricPowerRel_le_ker :
    symmetricPowerRel A M r ≤ LinearMap.ker
      ((SymmetricAlgebra.algHom A M).toLinearMap ∘ₗ TensorPower.toTensorAlgebra) := by
  rw [symmetricPowerRel, Submodule.span_le]
  rintro _ ⟨e, m, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.coe_comp,
    Function.comp_apply, TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply,
    AlgHom.toLinearMap_apply, map_list_prod, List.map_ofFn, List.prod_ofFn, sub_eq_zero]
  exact Equiv.prod_comp e (fun i => SymmetricAlgebra.algHom A M (TensorAlgebra.ι A (m i)))

variable (A M) in
/-- The map `Sym^r M → S(M)` onto the homogeneous component of degree `r` of the symmetric
algebra. -/
noncomputable def symmetricPowerToAlgebra :
    SymmetricPowerQuotient A M r →ₗ[A] SymmetricAlgebra A M :=
  (symmetricPowerRel A M r).liftQ _ (symmetricPowerRel_le_ker r)

lemma symmetricPowerToAlgebra_mk (x : ⨂[A]^r M) :
    symmetricPowerToAlgebra A M r (Submodule.Quotient.mk x) =
      SymmetricAlgebra.algHom A M (TensorPower.toTensorAlgebra x) := rfl

theorem symmetricAlgebraMap_toAlgebra (σ : A →+* B) (f : M →ₛₗ[σ] N)
    (x : SymmetricPowerQuotient A M r) :
    symmetricAlgebraMap σ f (symmetricPowerToAlgebra A M r x) =
      symmetricPowerToAlgebra B N r (symmetricPowerMap r σ f x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [symmetricPowerToAlgebra_mk, symmetricAlgebraMap_apply, symmetricAlgebraRingHom_algHom,
    ← tensorAlgebraMap_apply, tensorAlgebraMap_toTensorAlgebra]
  rfl

omit [AddCommGroup M] in
lemma append_comp_perm_left {i j : ℕ} (m : Fin i → M) (e : Equiv.Perm (Fin i)) (b : Fin j → M) :
    Fin.append (m ∘ e) b = Fin.append m b ∘
      (finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl _)).trans finSumFinEquiv)) := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp

omit [AddCommGroup M] in
lemma append_comp_perm_right {i j : ℕ} (a : Fin i → M) (m : Fin j → M) (e : Equiv.Perm (Fin j)) :
    Fin.append a (m ∘ e) = Fin.append a m ∘
      (finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl _) e).trans finSumFinEquiv)) := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp

/-- The multiplication `⨂^i M × ⨂^j M → ⨂^(i+j) M`, as a bilinear map. -/
noncomputable def tensorPowerMul (i j : ℕ) :
    ⨂[A]^i M →ₗ[A] ⨂[A]^j M →ₗ[A] ⨂[A]^(i + j) M :=
  (TensorProduct.mk A _ _).compr₂ (TensorPower.mulEquiv (R := A) (M := M)).toLinearMap

lemma tensorPowerMul_apply {i j : ℕ} (a : ⨂[A]^i M) (b : ⨂[A]^j M) :
    tensorPowerMul i j a b = @GradedMonoid.GMul.mul ℕ (fun n => ⨂[A]^n M) _ _ i j a b := rfl

lemma tensorPowerMul_tprod {i j : ℕ} (a : Fin i → M) (b : Fin j → M) :
    tensorPowerMul i j (PiTensorProduct.tprod A a) (PiTensorProduct.tprod A b) =
      PiTensorProduct.tprod A (Fin.append a b) :=
  TensorPower.tprod_mul_tprod A a b

lemma mem_span_tprod {n : ℕ} (z : ⨂[A]^n M) :
    z ∈ Submodule.span A (Set.range (PiTensorProduct.tprod A)) :=
  PiTensorProduct.span_tprod_eq_top (R := A) (s := fun _ : Fin n => M) ▸ Submodule.mem_top

theorem tensorPowerMul_mem_rel_left {i j : ℕ} {y : ⨂[A]^i M} (hy : y ∈ symmetricPowerRel A M i)
    (z : ⨂[A]^j M) : tensorPowerMul i j y z ∈ symmetricPowerRel A M (i + j) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, m, rfl⟩ := hy
    induction mem_span_tprod z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, rfl⟩ := hz
      rw [map_sub, LinearMap.sub_apply, tensorPowerMul_tprod, tensorPowerMul_tprod,
        append_comp_perm_left]
      exact Submodule.subset_span ⟨_, _, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [map_add]; exact add_mem hz hz'
    | smul a z _ hz => rw [map_smul]; exact Submodule.smul_mem _ a hz
  | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [map_add, LinearMap.add_apply]; exact add_mem hy hy'
  | smul a y _ hy => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ a hy

theorem tensorPowerMul_mem_rel_right {i j : ℕ} (y : ⨂[A]^i M) {z : ⨂[A]^j M}
    (hz : z ∈ symmetricPowerRel A M j) : tensorPowerMul i j y z ∈ symmetricPowerRel A M (i + j) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, m, rfl⟩ := hz
    induction mem_span_tprod y using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [map_sub, tensorPowerMul_tprod, tensorPowerMul_tprod, append_comp_perm_right]
      exact Submodule.subset_span ⟨_, _, rfl⟩
    | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
    | add y y' _ _ hy hy' => rw [map_add, LinearMap.add_apply]; exact add_mem hy hy'
    | smul a y _ hy => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ a hy
  | zero => rw [map_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [map_add]; exact add_mem hz hz'
  | smul a z _ hz => rw [map_smul]; exact Submodule.smul_mem _ a hz

variable (A M) in
/-- The submodule of the tensor algebra spanned by the images of the submodules
`symmetricPowerRel A M r ⊆ ⨂^r M`; it is the kernel of `T(M) → S(M)`
(`mem_symmetricKernel_iff`). -/
noncomputable def symmetricKernel : Submodule A (TensorAlgebra A M) :=
  Submodule.span A {t | ∃ (n : ℕ) (y : ⨂[A]^n M), y ∈ symmetricPowerRel A M n ∧
    t = TensorPower.toTensorAlgebra y}

lemma ι_eq_toTensorAlgebra (x : M) :
    TensorAlgebra.ι A x = TensorPower.toTensorAlgebra (PiTensorProduct.tprod A fun _ : Fin 1 => x) := by
  rw [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]
  simp

lemma toTensorAlgebra_tensorPowerMul {i j : ℕ} (a : ⨂[A]^i M) (b : ⨂[A]^j M) :
    TensorPower.toTensorAlgebra (tensorPowerMul i j a b) =
      TensorPower.toTensorAlgebra a * TensorPower.toTensorAlgebra b :=
  TensorPower.toTensorAlgebra_gMul a b

lemma ι_mul_mem_symmetricKernel (x : M) {t : TensorAlgebra A M} (ht : t ∈ symmetricKernel A M) :
    TensorAlgebra.ι A x * t ∈ symmetricKernel A M := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨n, y, hy, rfl⟩ := ht
    rw [ι_eq_toTensorAlgebra, ← toTensorAlgebra_tensorPowerMul]
    exact Submodule.subset_span ⟨_, _, tensorPowerMul_mem_rel_right _ hy, rfl⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add t t' _ _ ht ht' => rw [mul_add]; exact add_mem ht ht'
  | smul a t _ ht => rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ a ht

lemma mul_ι_mem_symmetricKernel (x : M) {t : TensorAlgebra A M} (ht : t ∈ symmetricKernel A M) :
    t * TensorAlgebra.ι A x ∈ symmetricKernel A M := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨n, y, hy, rfl⟩ := ht
    rw [ι_eq_toTensorAlgebra, ← toTensorAlgebra_tensorPowerMul]
    exact Submodule.subset_span ⟨_, _, tensorPowerMul_mem_rel_left hy _, rfl⟩
  | zero => rw [zero_mul]; exact zero_mem _
  | add t t' _ _ ht ht' => rw [add_mul]; exact add_mem ht ht'
  | smul a t _ ht => rw [Algebra.smul_mul_assoc]; exact Submodule.smul_mem _ a ht

lemma mul_mem_symmetricKernel_left (u : TensorAlgebra A M) {t : TensorAlgebra A M}
    (ht : t ∈ symmetricKernel A M) : u * t ∈ symmetricKernel A M := by
  induction u using TensorAlgebra.induction generalizing t with
  | algebraMap a => rw [← Algebra.smul_def]; exact Submodule.smul_mem _ a ht
  | ι x => exact ι_mul_mem_symmetricKernel x ht
  | mul u v hu hv => rw [mul_assoc]; exact hu (hv ht)
  | add u v hu hv => rw [add_mul]; exact add_mem (hu ht) (hv ht)

lemma mul_mem_symmetricKernel_right (u : TensorAlgebra A M) {t : TensorAlgebra A M}
    (ht : t ∈ symmetricKernel A M) : t * u ∈ symmetricKernel A M := by
  induction u using TensorAlgebra.induction generalizing t with
  | algebraMap a => rw [← Algebra.commutes, ← Algebra.smul_def]; exact Submodule.smul_mem _ a ht
  | ι x => exact mul_ι_mem_symmetricKernel x ht
  | mul u v hu hv => rw [← mul_assoc]; exact hv (hu ht)
  | add u v hu hv => rw [mul_add]; exact add_mem (hu ht) (hv ht)

variable (A M) in
/-- The ring congruence on the tensor algebra given by the two-sided ideal `symmetricKernel`. -/
noncomputable def symmetricKernelCon : RingCon (TensorAlgebra A M) where
  r a b := a - b ∈ symmetricKernel A M
  iseqv :=
    { refl := fun a => by rw [sub_self]; exact zero_mem _
      symm := fun h => by rw [← neg_sub]; exact neg_mem h
      trans := fun h h' => by rw [← sub_add_sub_cancel]; exact add_mem h h' }
  add' {a b c d} h h' := by rw [add_sub_add_comm]; exact add_mem h h'
  mul' {a b c d} h h' := by
    have e : a * c - b * d = (a - b) * c + b * (c - d) := by
      rw [sub_mul, mul_sub]; abel
    rw [e]
    exact add_mem (mul_mem_symmetricKernel_right c h) (mul_mem_symmetricKernel_left b h')

lemma mem_symmetricKernel_of_algHom_eq_zero {t : TensorAlgebra A M}
    (h : SymmetricAlgebra.algHom A M t = 0) : t ∈ symmetricKernel A M := by
  have h1 : TensorAlgebra.symRingCon A M t 0 :=
    (RingCon.eq (c := TensorAlgebra.symRingCon A M)).1
      (h.trans (map_zero (SymmetricAlgebra.algHom A M)).symm)
  have h2 : TensorAlgebra.symRingCon A M ≤ symmetricKernelCon A M := by
    change ringConGen _ ≤ _
    refine RingCon.ringConGen_le.2 fun x y hxy => ?_
    induction hxy with
    | mul_comm x y =>
      change _ - _ ∈ symmetricKernel A M
      rw [ι_eq_toTensorAlgebra, ι_eq_toTensorAlgebra, ← toTensorAlgebra_tensorPowerMul,
        ← toTensorAlgebra_tensorPowerMul, tensorPowerMul_tprod, tensorPowerMul_tprod, ← map_sub]
      refine Submodule.subset_span ⟨2, _, neg_mem_iff.1 ?_, rfl⟩
      rw [neg_sub]
      refine Submodule.subset_span ⟨Equiv.swap 0 1, Fin.append (fun _ : Fin 1 => x)
        (fun _ : Fin 1 => y), ?_⟩
      congr 2
      funext k
      fin_cases k <;> rfl
  have h3 : t - 0 ∈ symmetricKernel A M := h2 h1
  rwa [sub_zero] at h3

lemma toDirectSum_toTensorAlgebra {n : ℕ} (y : ⨂[A]^n M) :
    TensorAlgebra.toDirectSum (TensorPower.toTensorAlgebra y) = DirectSum.of _ n y := by
  induction mem_span_tprod y using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    rw [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.toDirectSum_tensorPower_tprod]
  | zero => rw [map_zero, map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, map_add]
  | smul a y _ hy => rw [map_smul, map_smul, hy, DirectSum.of_smul]

lemma toDirectSum_mem_rel {t : TensorAlgebra A M} (ht : t ∈ symmetricKernel A M) (n : ℕ) :
    TensorAlgebra.toDirectSum t n ∈ symmetricPowerRel A M n := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨k, y, hy, rfl⟩ := ht
    rw [toDirectSum_toTensorAlgebra]
    by_cases hk : k = n
    · subst hk
      rw [DirectSum.of_eq_same]
      exact hy
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk)]
      exact zero_mem _
  | zero => rw [map_zero, DirectSum.zero_apply]; exact zero_mem _
  | add t t' _ _ ht ht' => rw [map_add, DirectSum.add_apply]; exact add_mem ht ht'
  | smul a t _ ht => rw [map_smul, DirectSum.smul_apply]; exact Submodule.smul_mem _ a ht

variable (A M) in
/-- The direct sum of the quotient maps `⨂^r M → Sym^r M`. -/
noncomputable def directSumMkQ :
    (⨁ n, ⨂[A]^n M) →ₗ[A] ⨁ n, SymmetricPowerQuotient A M n :=
  DirectSum.toModule A ℕ _ fun n =>
    DirectSum.lof A ℕ (fun n => SymmetricPowerQuotient A M n) n ∘ₗ (symmetricPowerRel A M n).mkQ

lemma directSumMkQ_apply (d : ⨁ n, ⨂[A]^n M) (n : ℕ) :
    directSumMkQ A M d n = Submodule.Quotient.mk (d n) := by
  induction d using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, Submodule.Quotient.mk_zero]
  | of k y =>
    rw [← DirectSum.lof_eq_of A, directSumMkQ, DirectSum.toModule_lof, LinearMap.comp_apply,
      Submodule.mkQ_apply, DirectSum.lof_eq_of A, DirectSum.lof_eq_of A]
    by_cases hk : k = n
    · subst hk
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk),
        Submodule.Quotient.mk_zero]
  | add d d' hd hd' => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hd, hd',
      Submodule.Quotient.mk_add]

lemma directSumMkQ_surjective : Function.Surjective (directSumMkQ A M) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of k q =>
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨DirectSum.lof A ℕ (fun n => ⨂[A]^n M) k x, ?_⟩
    rw [directSumMkQ, DirectSum.toModule_lof, LinearMap.comp_apply, Submodule.mkQ_apply,
      DirectSum.lof_eq_of]
  | add y y' hy hy' =>
    obtain ⟨d, rfl⟩ := hy
    obtain ⟨d', rfl⟩ := hy'
    exact ⟨d + d', map_add _ _ _⟩

lemma toModule_symmetricPowerToAlgebra_directSumMkQ (d : ⨁ n, ⨂[A]^n M) :
    DirectSum.toModule A ℕ (SymmetricAlgebra A M) (fun n => symmetricPowerToAlgebra A M n)
        (directSumMkQ A M d) =
      SymmetricAlgebra.algHom A M (TensorAlgebra.ofDirectSum d) := by
  rw [← LinearMap.comp_apply, ← AlgHom.toLinearMap_apply, ← AlgHom.toLinearMap_apply,
    ← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext A fun n => LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, directSumMkQ, DirectSum.toModule_lof, Submodule.mkQ_apply,
    symmetricPowerToAlgebra_mk, AlgHom.toLinearMap_apply]
  exact congrArg _ (DirectSum.toModule_lof (M := fun i => ⨂[A]^i M)
    (φ := fun n => (TensorPower.toTensorAlgebra : ⨂[A]^n M →ₗ[A] TensorAlgebra A M)) A n x).symm

theorem symmetricPower_directSum_bijective :
    Function.Bijective (DirectSum.toModule A ℕ (SymmetricAlgebra A M)
      (fun n => symmetricPowerToAlgebra A M n)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨d, rfl⟩ := directSumMkQ_surjective y
    rw [toModule_symmetricPowerToAlgebra_directSumMkQ] at hy
    have hd := toDirectSum_mem_rel (mem_symmetricKernel_of_algHom_eq_zero hy)
    rw [TensorAlgebra.toDirectSum_ofDirectSum] at hd
    ext n
    rw [directSumMkQ_apply, DirectSum.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact hd n
  · intro s
    obtain ⟨t, rfl⟩ := SymmetricAlgebra.algHom_surjective A M s
    obtain ⟨d, rfl⟩ := Function.bijective_iff_has_inverse.2 ⟨TensorAlgebra.toDirectSum,
      TensorAlgebra.toDirectSum_ofDirectSum, TensorAlgebra.ofDirectSum_toDirectSum⟩ |>.2 t
    exact ⟨directSumMkQ A M d, toModule_symmetricPowerToAlgebra_directSumMkQ d⟩

theorem symmetricPower_mul_mem (r s : ℕ) (a : SymmetricPowerQuotient A M r)
    (b : SymmetricPowerQuotient A M s) :
    symmetricPowerToAlgebra A M r a * symmetricPowerToAlgebra A M s b ∈
      LinearMap.range (symmetricPowerToAlgebra A M (r + s)) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  refine ⟨Submodule.Quotient.mk (tensorPowerMul r s x y), ?_⟩
  rw [symmetricPowerToAlgebra_mk, symmetricPowerToAlgebra_mk, symmetricPowerToAlgebra_mk,
    toTensorAlgebra_tensorPowerMul, map_mul]

end SymmetricAlgebra

end SheafTensorOperations

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

open SheafTensorOperations SheafAlgebraOperations

/-- A **sheaf of `𝒪_X`-algebras** structure on an `𝒪_X`-module `A`: for every open `U` an
associative, unital, `𝒪_X(U)`-bilinear multiplication on `A(U)`, such that the restriction maps
preserve products and units. -/
abbrev ModuleSheafAlgebra (A : SheafOfModules.{u} (ringCatSheafOf R)) := PresheafAlgebra A.val

variable (r : ℕ) (F : SheafOfModules.{u} (ringCatSheafOf R))

section TensorAlgebraSheaf

/-- The presheaf of modules `U ↦ T(F(U))`, the tensor algebra of `F(U)` over `𝒪_X(U)`. -/
noncomputable def moduleSheafTensorAlgebraPresheaf :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfSemilinear (fun U => ModuleCat.of _ (TensorAlgebra _ (F.val.obj U)))
    (fun i => tensorAlgebraMap _ (F.val.restrictₛₗ i))
    (fun U x => tensorAlgebraMap_id (ringMap_id_apply U) _ (restrictₛₗ_id F.val U) x)
    (fun i j x => tensorAlgebraMap_comp (ringMap_comp_apply i j) _ _ _
      (restrictₛₗ_comp F.val i j) x)

/-- The presheaf of `𝒪_X`-algebras `U ↦ T(F(U))`. -/
noncomputable def moduleSheafTensorAlgebraPresheafAlgebra :
    PresheafAlgebra (moduleSheafTensorAlgebraPresheaf F) where
  mul :=
    { app U := algebraMulBilinear _ (TensorAlgebra _ (F.val.obj U))
      naturality i a b := tensorAlgebraMap_mul _ (F.val.restrictₛₗ i) a b }
  one U := (1 : TensorAlgebra _ (F.val.obj U))
  map_one i := map_one (tensorAlgebraRingHom _ (F.val.restrictₛₗ i))
  mul_assoc U a b c := _root_.mul_assoc (G := TensorAlgebra _ (F.val.obj U)) a b c
  one_mul U a := _root_.one_mul (M := TensorAlgebra _ (F.val.obj U)) a
  mul_one U a := _root_.mul_one (M := TensorAlgebra _ (F.val.obj U)) a

/-- The inclusion of the presheaf `U ↦ T^r(F(U))` into `U ↦ T(F(U))`. -/
noncomputable def moduleSheafTensorAlgebraPresheafι :
    moduleSheafTensorPowerPresheaf r F ⟶ moduleSheafTensorAlgebraPresheaf F where
  app U := ModuleCat.ofHom TensorPower.toTensorAlgebra
  naturality i := by
    ext x
    exact (tensorAlgebraMap_toTensorAlgebra r _ _ x).symm

theorem moduleSheafTensorAlgebraPresheaf_isGraded :
    (moduleSheafTensorAlgebraPresheafAlgebra F).IsGraded (fun r => moduleSheafTensorPowerPresheaf r F)
      (fun r => moduleSheafTensorAlgebraPresheafι r F) where
  bijective _ := toTensorAlgebra_directSum_bijective
  mul_mem _ r s a b := toTensorAlgebra_mul_mem r s a b

/-- **The tensor algebra of a module sheaf.** The `𝒪_X`-module `T(F)`, the sheafification of the
presheaf `U ↦ T(F(U))`; its sheaf of `𝒪_X`-algebras structure is
`moduleSheafTensorAlgebraStructure F`. -/
noncomputable def moduleSheafTensorAlgebra : SheafOfModules.{u} (ringCatSheafOf R) :=
  sheafify (moduleSheafTensorAlgebraPresheaf F)

/-- The sheaf of `𝒪_X`-algebras structure on `T(F)`, obtained by sheafifying the multiplication of
the presheaf of `𝒪_X`-algebras `U ↦ T(F(U))`. -/
noncomputable def moduleSheafTensorAlgebraStructure : ModuleSheafAlgebra (moduleSheafTensorAlgebra F) :=
  (moduleSheafTensorAlgebraPresheafAlgebra F).sheafification

/-- The canonical map `U ↦ T(F(U))` to `T(F)` is multiplicative. -/
theorem moduleSheafTensorAlgebra_mul_unit (U : (Opens X)ᵒᵖ)
    (a b : TensorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) :
    (moduleSheafTensorAlgebraStructure F).mul.app U
        ((sheafifyUnit (moduleSheafTensorAlgebraPresheaf F)).app U a)
        ((sheafifyUnit (moduleSheafTensorAlgebraPresheaf F)).app U b) =
      (sheafifyUnit (moduleSheafTensorAlgebraPresheaf F)).app U (a * b) :=
  (moduleSheafTensorAlgebraPresheafAlgebra F).sheafification_mul_unit U a b

/-- The canonical map `U ↦ T(F(U))` to `T(F)` is unital. -/
theorem moduleSheafTensorAlgebra_one (U : (Opens X)ᵒᵖ) :
    (moduleSheafTensorAlgebraStructure F).one U =
      (sheafifyUnit (moduleSheafTensorAlgebraPresheaf F)).app U
        (1 : TensorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) :=
  rfl

/-- The inclusion `T^r F → T(F)` of the homogeneous component of degree `r`. -/
noncomputable def moduleSheafTensorAlgebraι :
    moduleSheafTensorPower r F ⟶ moduleSheafTensorAlgebra F :=
  sheafifyMap (moduleSheafTensorAlgebraPresheafι r F)

/-- **`T(F)` is the direct sum of the tensor powers `T^r F`.** -/
noncomputable def moduleSheafTensorAlgebra_isColimit :
    IsColimit (Cofan.mk (moduleSheafTensorAlgebra F) fun r => moduleSheafTensorAlgebraι r F) :=
  (moduleSheafTensorAlgebraPresheaf_isGraded F).isColimit

/-- The multiplication `T^r F × T^s F → T^{r+s} F` of homogeneous sections. -/
noncomputable def moduleSheafTensorPowerMul (s : ℕ) :
    PresheafBilinear (moduleSheafTensorPower r F).val (moduleSheafTensorPower s F).val
      (moduleSheafTensorPower (r + s) F).val :=
  (moduleSheafTensorAlgebraPresheaf_isGraded F).sheafMul r s

/-- **The grading of `T(F)` is multiplicative:** the product of homogeneous sections of degrees `r`
and `s` is homogeneous of degree `r + s`. -/
theorem moduleSheafTensorAlgebra_mul_ι (s : ℕ) (U : (Opens X)ᵒᵖ)
    (a : (moduleSheafTensorPower r F).val.obj U) (b : (moduleSheafTensorPower s F).val.obj U) :
    (moduleSheafTensorAlgebraStructure F).mul.app U ((moduleSheafTensorAlgebraι r F).val.app U a)
        ((moduleSheafTensorAlgebraι s F).val.app U b) =
      (moduleSheafTensorAlgebraι (r + s) F).val.app U ((moduleSheafTensorPowerMul r F s).app U a b) :=
  (moduleSheafTensorAlgebraPresheaf_isGraded F).sheafification_mul_ι r s U a b

end TensorAlgebraSheaf

section ExteriorAlgebraSheaf

/-- The presheaf of modules `U ↦ ⋀(F(U))`, the exterior algebra of `F(U)` over `𝒪_X(U)`. -/
noncomputable def moduleSheafExteriorAlgebraPresheaf :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfSemilinear (fun U => ModuleCat.of _ (ExteriorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)))
    (fun i => exteriorAlgebraMap _ (F.val.restrictₛₗ i))
    (fun U x => exteriorAlgebraMap_id (ringMap_id_apply U) _ (restrictₛₗ_id F.val U) x)
    (fun i j x => exteriorAlgebraMap_comp (ringMap_comp_apply i j) _ _ _
      (restrictₛₗ_comp F.val i j) x)

/-- The presheaf of `𝒪_X`-algebras `U ↦ ⋀(F(U))`. -/
noncomputable def moduleSheafExteriorAlgebraPresheafAlgebra :
    PresheafAlgebra (moduleSheafExteriorAlgebraPresheaf F) where
  mul :=
    { app U := algebraMulBilinear _ (ExteriorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U))
      naturality i a b := exteriorAlgebraMap_mul _ (F.val.restrictₛₗ i) a b }
  one U := (1 : ExteriorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U))
  map_one i := map_one (exteriorAlgebraRingHom _ (F.val.restrictₛₗ i))
  mul_assoc U a b c := _root_.mul_assoc (G := ExteriorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) a b c
  one_mul U a := _root_.one_mul (M := ExteriorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) a
  mul_one U a := _root_.mul_one (M := ExteriorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) a

/-- The inclusion of the presheaf `U ↦ ⋀^r(F(U))` into `U ↦ ⋀(F(U))`. -/
noncomputable def moduleSheafExteriorAlgebraPresheafι :
    moduleSheafExteriorPowerPresheaf r F ⟶ moduleSheafExteriorAlgebraPresheaf F where
  app U := ModuleCat.ofHom (⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U]^r (F.val.obj U)).subtype
  naturality i := by
    ext x
    exact (exteriorAlgebraMap_coe r ((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom
      (F.val.restrictₛₗ i) x).symm

theorem moduleSheafExteriorAlgebraPresheaf_isGraded :
    (moduleSheafExteriorAlgebraPresheafAlgebra F).IsGraded
      (fun r => moduleSheafExteriorPowerPresheaf r F)
      (fun r => moduleSheafExteriorAlgebraPresheafι r F) where
  bijective _ := exteriorPower_directSum_bijective
  mul_mem _ r s a b := exteriorPower_mul_mem r s a b

/-- **The exterior algebra of a module sheaf.** The `𝒪_X`-module `⋀(F)`, the sheafification of the
presheaf `U ↦ ⋀(F(U))`; its sheaf of `𝒪_X`-algebras structure is
`moduleSheafExteriorAlgebraStructure F`. -/
noncomputable def moduleSheafExteriorAlgebra : SheafOfModules.{u} (ringCatSheafOf R) :=
  sheafify (moduleSheafExteriorAlgebraPresheaf F)

/-- The sheaf of `𝒪_X`-algebras structure on `⋀(F)`, obtained by sheafifying the multiplication
of the presheaf of `𝒪_X`-algebras `U ↦ ⋀(F(U))`. -/
noncomputable def moduleSheafExteriorAlgebraStructure :
    ModuleSheafAlgebra (moduleSheafExteriorAlgebra F) :=
  (moduleSheafExteriorAlgebraPresheafAlgebra F).sheafification

/-- The canonical map `U ↦ ⋀(F(U))` to `⋀(F)` is multiplicative. -/
theorem moduleSheafExteriorAlgebra_mul_unit (U : (Opens X)ᵒᵖ)
    (a b : ExteriorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) :
    (moduleSheafExteriorAlgebraStructure F).mul.app U
        ((sheafifyUnit (moduleSheafExteriorAlgebraPresheaf F)).app U a)
        ((sheafifyUnit (moduleSheafExteriorAlgebraPresheaf F)).app U b) =
      (sheafifyUnit (moduleSheafExteriorAlgebraPresheaf F)).app U (a * b) :=
  (moduleSheafExteriorAlgebraPresheafAlgebra F).sheafification_mul_unit U a b

/-- The canonical map `U ↦ ⋀(F(U))` to `⋀(F)` is unital. -/
theorem moduleSheafExteriorAlgebra_one (U : (Opens X)ᵒᵖ) :
    (moduleSheafExteriorAlgebraStructure F).one U =
      (sheafifyUnit (moduleSheafExteriorAlgebraPresheaf F)).app U
        (1 : ExteriorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) :=
  rfl

/-- The inclusion `⋀^r F → ⋀(F)` of the homogeneous component of degree `r`. -/
noncomputable def moduleSheafExteriorAlgebraι :
    moduleSheafExteriorPower r F ⟶ moduleSheafExteriorAlgebra F :=
  sheafifyMap (moduleSheafExteriorAlgebraPresheafι r F)

/-- **`⋀(F)` is the direct sum of the exterior powers `⋀^r F`.** -/
noncomputable def moduleSheafExteriorAlgebra_isColimit :
    IsColimit (Cofan.mk (moduleSheafExteriorAlgebra F) fun r => moduleSheafExteriorAlgebraι r F) :=
  (moduleSheafExteriorAlgebraPresheaf_isGraded F).isColimit

/-- The multiplication `⋀^r F × ⋀^s F → ⋀^{r+s} F` of homogeneous sections. -/
noncomputable def moduleSheafExteriorPowerMul (s : ℕ) :
    PresheafBilinear (moduleSheafExteriorPower r F).val (moduleSheafExteriorPower s F).val
      (moduleSheafExteriorPower (r + s) F).val :=
  (moduleSheafExteriorAlgebraPresheaf_isGraded F).sheafMul r s

/-- **The grading of `⋀(F)` is multiplicative:** the product of homogeneous sections of degrees `r`
and `s` is homogeneous of degree `r + s`. -/
theorem moduleSheafExteriorAlgebra_mul_ι (s : ℕ) (U : (Opens X)ᵒᵖ)
    (a : (moduleSheafExteriorPower r F).val.obj U) (b : (moduleSheafExteriorPower s F).val.obj U) :
    (moduleSheafExteriorAlgebraStructure F).mul.app U
        ((moduleSheafExteriorAlgebraι r F).val.app U a)
        ((moduleSheafExteriorAlgebraι s F).val.app U b) =
      (moduleSheafExteriorAlgebraι (r + s) F).val.app U
        ((moduleSheafExteriorPowerMul r F s).app U a b) :=
  (moduleSheafExteriorAlgebraPresheaf_isGraded F).sheafification_mul_ι r s U a b

end ExteriorAlgebraSheaf

section SymmetricAlgebraSheaf

/-- The presheaf of modules `U ↦ S(F(U))`, the symmetric algebra of `F(U)` over `𝒪_X(U)`. -/
noncomputable def moduleSheafSymmetricAlgebraPresheaf :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfSemilinear
    (fun U => ModuleCat.of _
      (SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)))
    (fun i => symmetricAlgebraMap _ (F.val.restrictₛₗ i))
    (fun U x => symmetricAlgebraMap_id (ringMap_id_apply U) _ (restrictₛₗ_id F.val U) x)
    (fun i j x => symmetricAlgebraMap_comp (ringMap_comp_apply i j) _ _ _
      (restrictₛₗ_comp F.val i j) x)

/-- The presheaf of `𝒪_X`-algebras `U ↦ S(F(U))`. -/
noncomputable def moduleSheafSymmetricAlgebraPresheafAlgebra :
    PresheafAlgebra (moduleSheafSymmetricAlgebraPresheaf F) where
  mul :=
    { app U := algebraMulBilinear _
        (SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U))
      naturality i a b := symmetricAlgebraMap_mul _ (F.val.restrictₛₗ i) a b }
  one U := (1 : SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U))
  map_one i := map_one (symmetricAlgebraRingHom _ (F.val.restrictₛₗ i))
  mul_assoc U a b c := _root_.mul_assoc
    (G := SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) a b c
  one_mul U a := _root_.one_mul
    (M := SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) a
  mul_one U a := _root_.mul_one
    (M := SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) a

/-- The presheaf of `𝒪_X`-algebras `U ↦ S(F(U))` is commutative. -/
theorem moduleSheafSymmetricAlgebraPresheafAlgebra_mul_comm (U : (Opens X)ᵒᵖ)
    (a b : SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) :
    (moduleSheafSymmetricAlgebraPresheafAlgebra F).mul.app U a b =
      (moduleSheafSymmetricAlgebraPresheafAlgebra F).mul.app U b a :=
  mul_comm a b

/-- The map from the presheaf `U ↦ Sym^r(F(U))` onto the degree-`r` part of `U ↦ S(F(U))`. -/
noncomputable def moduleSheafSymmetricAlgebraPresheafι :
    moduleSheafSymmetricPowerPresheaf r F ⟶ moduleSheafSymmetricAlgebraPresheaf F where
  app U := ModuleCat.ofHom
    (symmetricPowerToAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U) r)
  naturality i := by
    ext x
    exact (symmetricAlgebraMap_toAlgebra r ((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom
      (F.val.restrictₛₗ i) x).symm

theorem moduleSheafSymmetricAlgebraPresheaf_isGraded :
    (moduleSheafSymmetricAlgebraPresheafAlgebra F).IsGraded
      (fun r => moduleSheafSymmetricPowerPresheaf r F)
      (fun r => moduleSheafSymmetricAlgebraPresheafι r F) where
  bijective _ := symmetricPower_directSum_bijective
  mul_mem _ r s a b := symmetricPower_mul_mem r s a b

/-- **The symmetric algebra of a module sheaf.** The `𝒪_X`-module `S(F)`, the sheafification of
the presheaf `U ↦ S(F(U))`; its sheaf of `𝒪_X`-algebras structure is
`moduleSheafSymmetricAlgebraStructure F`. -/
noncomputable def moduleSheafSymmetricAlgebra : SheafOfModules.{u} (ringCatSheafOf R) :=
  sheafify (moduleSheafSymmetricAlgebraPresheaf F)

/-- The sheaf of `𝒪_X`-algebras structure on `S(F)`, obtained by sheafifying the multiplication
of the presheaf of `𝒪_X`-algebras `U ↦ S(F(U))`. -/
noncomputable def moduleSheafSymmetricAlgebraStructure :
    ModuleSheafAlgebra (moduleSheafSymmetricAlgebra F) :=
  (moduleSheafSymmetricAlgebraPresheafAlgebra F).sheafification

/-- The canonical map `U ↦ S(F(U))` to `S(F)` is multiplicative. -/
theorem moduleSheafSymmetricAlgebra_mul_unit (U : (Opens X)ᵒᵖ)
    (a b : SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) :
    (moduleSheafSymmetricAlgebraStructure F).mul.app U
        ((sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf F)).app U a)
        ((sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf F)).app U b) =
      (sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf F)).app U (a * b) :=
  (moduleSheafSymmetricAlgebraPresheafAlgebra F).sheafification_mul_unit U a b

/-- The canonical map `U ↦ S(F(U))` to `S(F)` is unital. -/
theorem moduleSheafSymmetricAlgebra_one (U : (Opens X)ᵒᵖ) :
    (moduleSheafSymmetricAlgebraStructure F).one U =
      (sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf F)).app U
        (1 : SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) :=
  rfl

/-- The inclusion `S^r F → S(F)` of the homogeneous component of degree `r`. -/
noncomputable def moduleSheafSymmetricAlgebraι :
    moduleSheafSymmetricPower r F ⟶ moduleSheafSymmetricAlgebra F :=
  sheafifyMap (moduleSheafSymmetricAlgebraPresheafι r F)

/-- **`S(F)` is the direct sum of the symmetric powers `S^r F`.** -/
noncomputable def moduleSheafSymmetricAlgebra_isColimit :
    IsColimit (Cofan.mk (moduleSheafSymmetricAlgebra F) fun r => moduleSheafSymmetricAlgebraι r F) :=
  (moduleSheafSymmetricAlgebraPresheaf_isGraded F).isColimit

/-- The multiplication `S^r F × S^s F → S^{r+s} F` of homogeneous sections. -/
noncomputable def moduleSheafSymmetricPowerMul (s : ℕ) :
    PresheafBilinear (moduleSheafSymmetricPower r F).val (moduleSheafSymmetricPower s F).val
      (moduleSheafSymmetricPower (r + s) F).val :=
  (moduleSheafSymmetricAlgebraPresheaf_isGraded F).sheafMul r s

/-- **The grading of `S(F)` is multiplicative:** the product of homogeneous sections of degrees `r`
and `s` is homogeneous of degree `r + s`. -/
theorem moduleSheafSymmetricAlgebra_mul_ι (s : ℕ) (U : (Opens X)ᵒᵖ)
    (a : (moduleSheafSymmetricPower r F).val.obj U) (b : (moduleSheafSymmetricPower s F).val.obj U) :
    (moduleSheafSymmetricAlgebraStructure F).mul.app U
        ((moduleSheafSymmetricAlgebraι r F).val.app U a)
        ((moduleSheafSymmetricAlgebraι s F).val.app U b) =
      (moduleSheafSymmetricAlgebraι (r + s) F).val.app U
        ((moduleSheafSymmetricPowerMul r F s).app U a b) :=
  (moduleSheafSymmetricAlgebraPresheaf_isGraded F).sheafification_mul_ι r s U a b

end SymmetricAlgebraSheaf

end Hartshorne
