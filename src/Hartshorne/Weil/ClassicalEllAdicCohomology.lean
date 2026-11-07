/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Weil.TorsionEtaleCohomology

/-!
# The classical inverse system of torsion étale cohomology

For a scheme `X`, a natural number `ℓ` and a degree `i`, the reduction maps
`ℤ/ℓ^s → ℤ/ℓ^r` (`r ≤ s`) of the constant coefficient sheaves on the small étale site form
an inverse system indexed by `ℕ`, and applying the `i`-th right derived functor of global
sections gives the inverse system

`⋯ → H^i_et(X, ℤ/ℓ^(r+1)) → H^i_et(X, ℤ/ℓ^r) → ⋯`

of abelian groups.  The classical `ℓ`-adic group `H^i_classical(X, ℤ_ℓ)` is its ordinary
inverse limit in abelian groups.  No surjectivity or Mittag-Leffler property of the transition
maps is asserted here.

As in `Hartshorne.Weil.ConstantTorsionEtaleSheaf`, the system is indexed by every natural
number; its zeroth stage `H^i_et(X, ℤ/ℓ^0)` has trivial coefficients and does not change the
limit.  The system has the same type `ℕᵒᵖ ⥤ AddCommGrpCat` as the inverse systems of
`Hartshorne.Scheme.InverseSystemMittagLeffler`, so the Mittag-Leffler API applies to it directly.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- The reduction maps compose: reducing from `ℤ/ℓ^t` to `ℤ/ℓ^s` and then to `ℤ/ℓ^r` is the
reduction from `ℤ/ℓ^t` to `ℤ/ℓ^r`. -/
theorem constantTorsionEtaleSheafReduction_comp (X : Scheme.{u}) (ℓ : ℕ) {r s t : ℕ}
    (hrs : r ≤ s) (hst : s ≤ t) :
    X.constantTorsionEtaleSheafReduction ℓ hst ≫ X.constantTorsionEtaleSheafReduction ℓ hrs =
      X.constantTorsionEtaleSheafReduction ℓ (hrs.trans hst) := by
  unfold constantTorsionEtaleSheafReduction constantTorsionEtaleSheaf
  rw [← Functor.map_comp, ← Functor.map_comp, ← AddCommGrpCat.ofHom_comp,
    ← ZMod.castHom_comp (pow_dvd_pow ℓ hrs) (pow_dvd_pow ℓ hst)]

/-- The reduction from `ℤ/ℓ^r` to itself is the identity. -/
theorem constantTorsionEtaleSheafReduction_refl (X : Scheme.{u}) (ℓ r : ℕ) :
    X.constantTorsionEtaleSheafReduction ℓ (le_refl r) = 𝟙 _ := by
  have h : ZMod.castHom (pow_dvd_pow ℓ (le_refl r)) (ZMod (ℓ ^ r)) = RingHom.id _ :=
    Subsingleton.elim _ _
  simp only [constantTorsionEtaleSheafReduction, h]
  exact (congrArg (constantSheaf _ _).map (AddCommGrpCat.uliftFunctor.map_id _)).trans
    ((constantSheaf _ _).map_id _)

/-- The inverse system `r ↦ ℤ/ℓ^r` of constant torsion sheaves on the small étale site of `X`,
with the reduction maps as transition maps. -/
@[simps]
noncomputable def constantTorsionEtaleSheafSystem (X : Scheme.{u}) (ℓ : ℕ) :
    ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u} where
  obj r := X.constantTorsionEtaleSheaf ℓ r.unop
  map f := X.constantTorsionEtaleSheafReduction ℓ (leOfHom f.unop)
  map_id r := X.constantTorsionEtaleSheafReduction_refl ℓ r.unop
  map_comp _ _ := (X.constantTorsionEtaleSheafReduction_comp ℓ _ _).symm

/-- The classical inverse system `r ↦ H^i_et(X, ℤ/ℓ^r)`: its transition maps
`H^i_et(X, ℤ/ℓ^s) ⟶ H^i_et(X, ℤ/ℓ^r)` (`r ≤ s`) are induced by the reduction maps of the
coefficient sheaves. -/
noncomputable def torsionEtaleCohomologySystem (X : Scheme.{u}) (ℓ i : ℕ) : ℕᵒᵖ ⥤ Ab.{u} :=
  X.constantTorsionEtaleSheafSystem ℓ ⋙ (Sheaf.Γ X.smallEtaleTopology Ab.{u}).rightDerived i

@[simp]
theorem torsionEtaleCohomologySystem_obj (X : Scheme.{u}) (ℓ i : ℕ) (r : ℕᵒᵖ) :
    (X.torsionEtaleCohomologySystem ℓ i).obj r = X.torsionEtaleCohomology ℓ r.unop i :=
  rfl

theorem torsionEtaleCohomologySystem_map (X : Scheme.{u}) (ℓ i : ℕ) {r s : ℕᵒᵖ} (f : r ⟶ s) :
    (X.torsionEtaleCohomologySystem ℓ i).map f =
      ((Sheaf.Γ X.smallEtaleTopology Ab.{u}).rightDerived i).map
        (X.constantTorsionEtaleSheafReduction ℓ (leOfHom f.unop)) :=
  rfl

/-- The classical integral `ℓ`-adic cohomology group
`H^i_classical(X, ℤ_ℓ) = lim_r H^i_et(X, ℤ/ℓ^r)`: the ordinary inverse limit, in abelian
groups, of the classical inverse system of torsion étale cohomology groups. -/
noncomputable def classicalEllAdicCohomology (X : Scheme.{u}) (ℓ i : ℕ) : Ab.{u} :=
  limit (X.torsionEtaleCohomologySystem ℓ i)

end AlgebraicGeometry.Scheme
