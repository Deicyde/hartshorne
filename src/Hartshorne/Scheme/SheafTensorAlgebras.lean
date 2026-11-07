/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
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

end Hartshorne
