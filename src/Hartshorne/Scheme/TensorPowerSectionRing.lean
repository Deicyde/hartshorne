/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SheafTensorAlgebras

/-!
# The section ring of the tensor powers of a module sheaf

For a sheaf of modules `F` on a ringed space, the sections over an open `U` of the tensor powers
`F^{⊗ n}` form a graded ring `⨁ₙ Γ(U, F^{⊗ n})`, with multiplication induced by the tensor
product. It is computed inside the sections of the tensor algebra sheaf `T(F)`, into which each
`Γ(U, F^{⊗ n})` embeds.
-/

open CategoryTheory TopologicalSpace Opposite Limits
open scoped TensorProduct DirectSum

namespace Hartshorne

universe u

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (F : SheafOfModules.{u} (ringCatSheafOf R))

namespace TensorPowerSectionRing

open SheafAlgebraOperations

/-- The projection `T(F) ⟶ F^{⊗ r}` onto the component of degree `r`. -/
noncomputable def proj (r : ℕ) : moduleSheafTensorAlgebra F ⟶ moduleSheafTensorPower r F :=
  (moduleSheafTensorAlgebra_isColimit F).desc
    (Cofan.mk (moduleSheafTensorPower r F) fun s => if h : s = r then eqToHom (by subst h; rfl) else 0)

@[reassoc (attr := simp)]
theorem ι_proj (r : ℕ) : moduleSheafTensorAlgebraι r F ≫ proj F r = 𝟙 _ := by
  have := (moduleSheafTensorAlgebra_isColimit F).fac
    (Cofan.mk (moduleSheafTensorPower r F) fun s => if h : s = r then eqToHom (by subst h; rfl) else 0) ⟨r⟩
  simpa [proj] using this

/-- The inclusion `F^{⊗ r} ⟶ T(F)` is injective on sections. -/
theorem ι_injective (r : ℕ) (U : (Opens X)ᵒᵖ) :
    Function.Injective ((moduleSheafTensorAlgebraι r F).val.app U) := by
  intro a b h
  have h' := congrArg ((proj F r).val.app U) h
  have e : ∀ c, (proj F r).val.app U ((moduleSheafTensorAlgebraι r F).val.app U c) = c := fun c =>
    congrArg (fun φ => φ.val.app U c) (ι_proj F r)
  rwa [e, e] at h'

variable (U : (Opens X)ᵒᵖ)

/-- The sections `Γ(U, F^{⊗ n})`. -/
abbrev Component (n : ℕ) : Type u := (moduleSheafTensorPower n F).val.obj U

/-- The unit section `1 ∈ Γ(U, F^{⊗ 0})`. -/
noncomputable def oneSec : Component F U 0 :=
  (sheafifyUnit (moduleSheafTensorPowerPresheaf 0 F)).app U
    (@GradedMonoid.GOne.one _
      (fun n => ⨂[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U]^n (F.val.obj U)) _ _)

theorem ι_oneSec :
    (moduleSheafTensorAlgebraι 0 F).val.app U (oneSec F U) =
      (moduleSheafTensorAlgebraStructure F).one U := by
  rw [moduleSheafTensorAlgebra_one]
  exact (sheafifyMap_unit (moduleSheafTensorAlgebraPresheafι 0 F) U _).trans
    (congrArg _ TensorPower.toTensorAlgebra_gOne)

/-- The product `Γ(U, F^{⊗ m}) × Γ(U, F^{⊗ n}) → Γ(U, F^{⊗ (m + n)})`. -/
noncomputable def mul {m n : ℕ} (a : Component F U m) (b : Component F U n) : Component F U (m + n) :=
  (moduleSheafTensorPowerMul m F n).app U a b

theorem ι_mul {m n : ℕ} (a : Component F U m) (b : Component F U n) :
    (moduleSheafTensorAlgebraι (m + n) F).val.app U (mul F U a b) =
      (moduleSheafTensorAlgebraStructure F).mul.app U
        ((moduleSheafTensorAlgebraι m F).val.app U a) ((moduleSheafTensorAlgebraι n F).val.app U b) :=
  (moduleSheafTensorAlgebra_mul_ι m F n U a b).symm

theorem sigma_ext {i j : ℕ} (h : i = j) {a : Component F U i} {b : Component F U j}
    (e : (moduleSheafTensorAlgebraι i F).val.app U a = (moduleSheafTensorAlgebraι j F).val.app U b) :
    (⟨i, a⟩ : GradedMonoid (Component F U)) = ⟨j, b⟩ := by
  subst h
  rw [ι_injective F i U e]

noncomputable instance : GradedMonoid.GOne (Component F U) := ⟨oneSec F U⟩

noncomputable instance : GradedMonoid.GMul (Component F U) := ⟨fun a b => mul F U a b⟩

noncomputable instance : GradedMonoid.GMonoid (Component F U) where
  one_mul := fun ⟨n, a⟩ => sigma_ext F U (zero_add n) <| by
    change (moduleSheafTensorAlgebraι (0 + n) F).val.app U (mul F U (oneSec F U) a) = _
    rw [ι_mul, ι_oneSec, (moduleSheafTensorAlgebraStructure F).one_mul]
  mul_one := fun ⟨n, a⟩ => sigma_ext F U (add_zero n) <| by
    change (moduleSheafTensorAlgebraι (n + 0) F).val.app U (mul F U a (oneSec F U)) = _
    rw [ι_mul, ι_oneSec, (moduleSheafTensorAlgebraStructure F).mul_one]
  mul_assoc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => sigma_ext F U (add_assoc i j k) <| by
    change (moduleSheafTensorAlgebraι (i + j + k) F).val.app U (mul F U (mul F U a b) c) =
      (moduleSheafTensorAlgebraι (i + (j + k)) F).val.app U (mul F U a (mul F U b c))
    rw [ι_mul, ι_mul, ι_mul, ι_mul, (moduleSheafTensorAlgebraStructure F).mul_assoc]

noncomputable instance : DirectSum.GSemiring (Component F U) where
  mul_zero a := by
    change mul F U a 0 = 0
    exact LinearMap.map_zero _
  zero_mul b := by
    change mul F U 0 b = 0
    rw [mul, LinearMap.map_zero₂]
  mul_add a b c := by
    change mul F U a (b + c) = mul F U a b + mul F U a c
    exact LinearMap.map_add _ _ _
  add_mul a b c := by
    change mul F U (a + b) c = mul F U a c + mul F U b c
    rw [mul, mul, mul, LinearMap.map_add₂]
  natCast n := n • oneSec F U
  natCast_zero := zero_smul _ _
  natCast_succ n := succ_nsmul _ _

noncomputable instance : DirectSum.GRing (Component F U) where
  intCast n := n • oneSec F U
  intCast_ofNat _ := natCast_zsmul _ _
  intCast_negSucc_ofNat _ := negSucc_zsmul _ _

/-- **The section ring** `⨁ₙ Γ(U, F^{⊗ n})`. -/
noncomputable example : Ring (DirectSum ℕ (Component F U)) := inferInstance

end TensorPowerSectionRing

end Hartshorne
