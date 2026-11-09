/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.SurfaceCurveConvention

/-!
# Local equations of curves on a surface

Hartshorne, *Algebraic Geometry*, V.1 (p. 360) and V.3 (p. 389) use local equations of a curve
`C` on a surface at a point `P`: an element `f` of `𝒪_{X,P}` whose divisor agrees with `C` near
`P`.

* `Hartshorne.Surface.IsLocalEquation D P f`: `f ∈ 𝒪_{X,P}` is nonzero and, on some open
  neighbourhood `U` of `P`, `ord_y(f) = D(y)` for every codimension-one point `y ∈ U`.
* `Hartshorne.Surface.exists_isLocalEquation`: an effective divisor has a local equation at every
  point (the surface is locally factorial, so Weil divisors are Cartier).
* `Hartshorne.Surface.IsLocalEquation.associated`: two local equations differ by a unit of
  `𝒪_{X,P}`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Order TopologicalSpace

namespace Hartshorne

namespace Surface

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Surface k)

/-- `f ∈ 𝒪_{X,P}` is a **local equation** of the divisor `D` at `P`: `f ≠ 0` and on some open
neighbourhood `U` of `P` the divisor of `f` is `D`, i.e. `ord_y(f) = D(y)` for every
codimension-one point `y ∈ U`. -/
def IsLocalEquation (D : S.X.WeilDivisor) (P : S.X) (f : S.X.presheaf.stalk P) : Prop :=
  f ≠ 0 ∧ ∃ U : S.X.Opens, P ∈ U ∧ ∀ y ∈ U, coheight y = 1 →
    S.X.ord (algebraMap (S.X.presheaf.stalk P) S.X.functionField f) y = D.1 y

variable {S}

/-- An effective divisor on a surface has a local equation at every point. -/
theorem exists_isLocalEquation (D : S.Curve) (P : S.X) :
    ∃ f, S.IsLocalEquation D.1 P f := by
  set C := S.weilCartierEquiv D.1
  set U := (C.localEquation P).1
  have hPU : P ∈ U := C.mem_localEquation P
  have hrep := C.restrict_localEquation P
  set q : S.X.functionFieldˣ := Scheme.totalQuotientUnitsEquivFunctionField U
    (Scheme.genericPoint_mem_opens_of_mem hPU) (C.localEquation P).2
  have hCD : Scheme.cartierToWeil C = D.1 := (S.weilCartierEquiv.symm_apply_apply D.1)
  have hord : ∀ y ∈ U, S.X.ord (q : S.X.functionField) y = D.1.1 y := by
    intro y hy
    rw [← hCD, Scheme.cartierToWeil_apply C _ hrep hy]
  have : Nonempty U := ⟨⟨P, hPU⟩⟩
  have : Hartshorne.IsNormal S.X := Scheme.isNormal_of_isLocallyFactorial S.isLocallyFactorial
  obtain ⟨a, ha⟩ := Scheme.exists_germToFunctionField_eq_of_ord_nonneg_of_opens q.ne_zero
    fun y hy _ ↦ by rw [hord y hy]; exact D.2 y
  have halg : algebraMap (S.X.presheaf.stalk P) S.X.functionField
      (S.X.presheaf.germ U P hPU a) = q := by
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, ha]
  refine ⟨S.X.presheaf.germ U P hPU a, fun h0 ↦ q.ne_zero ?_, U, hPU, fun y hy _ ↦ ?_⟩
  · rw [← halg, h0, map_zero]
  · rw [halg, hord y hy]

/-- Two local equations of the same divisor at `P` differ by a unit of `𝒪_{X,P}`. -/
theorem IsLocalEquation.associated {D : S.X.WeilDivisor} {P : S.X}
    {f f' : S.X.presheaf.stalk P} (hf : S.IsLocalEquation D P f)
    (hf' : S.IsLocalEquation D P f') : Associated f f' := by
  obtain ⟨hf0, U, hPU, hU⟩ := hf
  obtain ⟨hf0', U', hPU', hU'⟩ := hf'
  set K := S.X.functionField
  have hinj : Function.Injective (algebraMap (S.X.presheaf.stalk P) K) :=
    IsFractionRing.injective _ _
  have ha0 : algebraMap (S.X.presheaf.stalk P) K f ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 hf0
  have ha0' : algebraMap (S.X.presheaf.stalk P) K f' ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 hf0'
  set q : Kˣ := Units.mk0 _ (div_ne_zero ha0' ha0)
  have hPW : P ∈ U ⊓ U' := ⟨hPU, hPU'⟩
  have : Nonempty (U ⊓ U' : S.X.Opens) := ⟨⟨P, hPW⟩⟩
  have : Hartshorne.IsNormal S.X := Scheme.isNormal_of_isLocallyFactorial S.isLocallyFactorial
  obtain ⟨a, ha⟩ := Scheme.exists_unit_germToFunctionField_eq_of_ord_eq_zero (V := U ⊓ U') q
    fun y hy hy1 ↦ by
    rw [Units.val_mk0, div_eq_mul_inv, S.X.ord_mul ha0' (inv_ne_zero ha0),
      Scheme.ord_inv_eq_neg ha0, hU y hy.1 hy1, hU' y hy.2 hy1, add_neg_cancel]
  refine ⟨(a.map (S.X.presheaf.germ (U ⊓ U') P hPW).hom.toMonoidHom), hinj ?_⟩
  change algebraMap _ K (f * S.X.presheaf.germ (U ⊓ U') P hPW (a : Γ(S.X, U ⊓ U'))) = _
  rw [map_mul, Scheme.algebraMap_germ_eq_germToFunctionField, ha, Units.val_mk0,
    mul_div_cancel₀ _ ha0]

end

end Surface

end Hartshorne
