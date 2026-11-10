/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.IdealPowerProduct
import Hartshorne.Scheme.ClosedImmersionIdealSheaf

/-!
# Quasi-coherent ideal subsheaves and ideal sheaf data

Hartshorne, *Algebraic Geometry*, II.5 (pp. 115–116).

For a scheme `X`, a *quasi-coherent ideal subsheaf* of `𝒪_X` is a family of ideals
`I(U) ⊆ Γ(U, 𝒪_X)`, stable under restriction and local (a sub-`𝒪_X`-module sheaf of `𝒪_X`), which
is quasi-coherent as an `𝒪_X`-module (`Hartshorne.QuasicoherentIdealSubsheaf`). Mathlib's
`X.IdealSheafData` stores instead a compatible family of ideals on the affine opens only.

`Hartshorne.quasicoherentIdealSubsheafEquiv` identifies the two:
* a quasi-coherent ideal subsheaf `I` goes to its ideals `Γ(U, I) ⊆ Γ(U, 𝒪_X)` on affine opens `U`
  (`quasicoherentIdealSubsheafEquiv_ideal`); they are compatible with restriction to basic opens
  because `I` is quasi-coherent;
* ideal sheaf data `J` goes to the subsheaf of sections lying locally in `J(V)` on affine opens
  `V` (`ArtinReesKernelSheaf.powSmul J 1 ⊤`), which is quasi-coherent with sections `J(V)` over
  every affine open `V`.

On an affine open `U`, `I|_U` is the tilde sheaf of the ideal `Γ(U, I)`
(`QuasicoherentIdealSubsheaf.restrictTildeIso`).
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

open ArtinReesKernelSheaf

variable (X : Scheme.{u})

/-- **Quasi-coherent ideal subsheaves** of `𝒪_X`: sub-`𝒪_X`-module sheaves of `𝒪_X` (local
families of ideals `I(U) ⊆ Γ(U, 𝒪_X)` stable under restriction) which are quasi-coherent. -/
@[ext]
structure QuasicoherentIdealSubsheaf where
  /-- The ideals `I(U) ⊆ Γ(U, 𝒪_X)`. -/
  carrier : (SheafOfModules.unit X.ringCatSheaf : X.Modules).val.Submodule
  isLocal : IsLocal carrier
  isQuasicoherent : (toModules carrier isLocal).IsQuasicoherent

variable {X}

namespace QuasicoherentIdealSubsheaf

/-- The `𝒪_X`-module `I` of a quasi-coherent ideal subsheaf. -/
abbrev toModules (I : QuasicoherentIdealSubsheaf X) : X.Modules :=
  ArtinReesKernelSheaf.toModules I.carrier I.isLocal

/-- The ideal `I(U) ⊆ Γ(U, 𝒪_X)`. -/
def ideal (I : QuasicoherentIdealSubsheaf X) (U : X.Opens) : Ideal Γ(X, U) :=
  sub I.carrier U

/-- The ideals `Γ(U, I)` of a quasi-coherent ideal subsheaf on affine opens are compatible with
restriction to basic opens. -/
theorem map_ideal_basicOpen (I : QuasicoherentIdealSubsheaf X) (U : X.affineOpens)
    (f : Γ(X, U)) :
    (I.ideal U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      I.ideal (X.affineBasicOpen f) := by
  have := I.isQuasicoherent
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact res_mem I.carrier (X.basicOpen_le f) hr
  · intro t ht
    obtain ⟨n, s, hs⟩ := exists_pow_smul_extension_of_isAffineOpen I.toModules U.2 f
      (⟨t, ht⟩ : I.carrier.obj (op (X.basicOpen f)))
    have hs' : X.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (s : I.carrier.obj (op (U : X.Opens))).1 =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n * t :=
      congrArg Subtype.val hs
    have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n) :=
      (X.toRingedSpace.isUnit_res_basicOpen f).pow n
    have ht' : t = (hu.unit⁻¹ : Γ(X, X.basicOpen f)ˣ).1 *
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op
          (s : I.carrier.obj (op (U : X.Opens))).1 := by
      rw [hs', ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [ht']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (s : I.carrier.obj (op (U : X.Opens))).2)

/-- The ideal sheaf data of a quasi-coherent ideal subsheaf: its ideals on affine opens. -/
def toIdealSheafData (I : QuasicoherentIdealSubsheaf X) : X.IdealSheafData where
  ideal U := I.ideal U
  map_ideal_basicOpen U f := I.map_ideal_basicOpen U f

end QuasicoherentIdealSubsheaf

/-- The quasi-coherent ideal subsheaf of ideal sheaf data `J`: the sections lying, near every
point, in `J(V)` on an affine open `V`. -/
def IdealSheafData.toQuasicoherentIdealSubsheaf (J : X.IdealSheafData) :
    QuasicoherentIdealSubsheaf X where
  carrier := powSmul J 1 ⊤
  isLocal := isLocal_powSmul J 1 ⊤
  isQuasicoherent := by
    have := ClosedImmersionIdeal.isQuasicoherent_unit X
    have := isQuasicoherent_top (E := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    exact isQuasicoherent_powSmul J 1 isLocal_top

/-- `J(V) • Γ(V, 𝒪_X) = J(V)`. -/
theorem ideal_pow_one_smul_top (U : X.Opens) (J : Ideal Γ(X, U)) :
    (J ^ 1 • (⊤ : Submodule Γ(X, U) Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)) :
      Ideal Γ(X, U)) = J := by
  rw [pow_one]
  exact Ideal.mul_top J

/-- Over every affine open `V`, the sections of the subsheaf of `J` are `J(V)`. -/
theorem IdealSheafData.ideal_toQuasicoherentIdealSubsheaf (J : X.IdealSheafData)
    (V : X.affineOpens) : J.toQuasicoherentIdealSubsheaf.ideal V = J.ideal V := by
  have := ClosedImmersionIdeal.isQuasicoherent_unit X
  have := isQuasicoherent_top (E := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  change sub (powSmul J 1 ⊤) V = _
  rw [sub_powSmul_eq J 1 isLocal_top V]
  exact ideal_pow_one_smul_top _ _

/-- **Quasi-coherent ideal subsheaves of `𝒪_X` are ideal sheaf data.** For a scheme `X`,
quasi-coherent ideal subsheaves `I ⊆ 𝒪_X` correspond to Mathlib's `X.IdealSheafData`
(compatible ideals on affine opens): `I` goes to its ideals `Γ(U, I) ⊆ Γ(U, 𝒪_X)` on affine
opens `U`. -/
def quasicoherentIdealSubsheafEquiv : QuasicoherentIdealSubsheaf X ≃ X.IdealSheafData where
  toFun I := I.toIdealSheafData
  invFun J := J.toQuasicoherentIdealSubsheaf
  left_inv I := by
    have hfam : ∀ V : X.affineOpens,
        (powSmulFamily I.toIdealSheafData 1 ⊤).obj V = sub I.carrier V := fun V =>
      ideal_pow_one_smul_top _ _
    refine QuasicoherentIdealSubsheaf.ext (le_antisymm ?_ ?_)
    · exact (powSmulFamily I.toIdealSheafData 1 ⊤).closure_le I.isLocal fun V => (hfam V).le
    · intro U s hs x hx
      obtain ⟨V, hVU, hxV⟩ := exists_affine_le hx
      exact ⟨V, hVU, hxV, (hfam V).ge (res_mem I.carrier hVU hs)⟩
  right_inv J := IdealSheafData.ext (funext fun V => J.ideal_toQuasicoherentIdealSubsheaf V)

/-- The ideal sheaf data of `I` has, on each affine open `U`, the ideal `Γ(U, I)`. -/
theorem quasicoherentIdealSubsheafEquiv_ideal (I : QuasicoherentIdealSubsheaf X)
    (U : X.affineOpens) : (quasicoherentIdealSubsheafEquiv I).ideal U = I.ideal U :=
  rfl

/-- The quasi-coherent ideal subsheaf of `J` has, on each affine open `U`, the ideal `J(U)`. -/
theorem quasicoherentIdealSubsheafEquiv_symm_ideal (J : X.IdealSheafData) (U : X.affineOpens) :
    (quasicoherentIdealSubsheafEquiv.symm J).ideal U = J.ideal U :=
  J.ideal_toQuasicoherentIdealSubsheaf U

/-- **The affine description.** On an affine open `U`, a quasi-coherent ideal subsheaf `I`
restricts to the tilde sheaf of the ideal `Γ(U, I) ⊆ Γ(U, 𝒪_X)`. -/
def QuasicoherentIdealSubsheaf.restrictTildeIso (I : QuasicoherentIdealSubsheaf X)
    (U : X.affineOpens) :
    specRestriction I.toModules U ≅ tilde (ModuleCat.of Γ(X, (U : X.Opens)) (I.ideal U)) :=
  haveI : IsIso (specRestriction I.toModules U).fromTildeΓ :=
    isIso_fromTildeΓ_iff.mpr
      ((QuasicoherentAbelianAux.isQuasicoherent_iff_forall_essImage _).mp I.isQuasicoherent U)
  (asIso (specRestriction I.toModules U).fromTildeΓ).symm ≪≫
    (tilde.functor _).mapIso (CoherentAux.sectionsEquiv I.toModules U.2).symm.toModuleIso

end Hartshorne
