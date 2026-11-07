/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
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

end Hartshorne
