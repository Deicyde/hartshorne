/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFibreRank
import Hartshorne.Scheme.Differentials.RelativeDifferentialsQuasicoherent

/-!
# Fibres of the relative differential sheaf on an affine open

Let `f : X ⟶ Y` be a morphism of schemes, `U ⊆ X` and `V ⊆ Y` affine opens with
`U ⊆ f⁻¹ V`, and put `A = Γ(Y, V)`, `B = Γ(X, U)`. Since `Ω_{X/Y}|_U ≅ (Ω_{B/A})~`, the fibre
`(Ω_{X/Y})_x ⊗ k(x)` at the point `x ∈ U` corresponding to a prime `q ⊂ B` has the same dimension
as `κ(q) ⊗_B Ω_{B/A}`.

## Main results

* `Hartshorne.finrank_fibre_eq_of_iso_tilde`: for an `𝒪_{Spec R}`-module `G ≅ M~` and a point
  `y`, `dim_{k(y)} (G_y ⊗ k(y)) = dim_{κ(y)} (κ(y) ⊗_R M)`.
* `Hartshorne.finrank_fibre_relativeDifferentials_affine`: the comparison for `Ω_{X/Y}` on an
  affine open.
-/

open CategoryTheory TensorProduct IsLocalRing Module

namespace Hartshorne

open AlgebraicGeometry FreeLocusAux

universe u

noncomputable section

attribute [local instance] freeLocusStalkAlgebra freeLocus_asIdeal_isPrime
  freeLocus_stalk_isLocalization freeLocusStalkModule freeLocus_stalk_isScalarTower

/-- The fibre of an `𝒪_{Spec R}`-module `G ≅ M~` at `y` has dimension
`dim_{κ(y)} (κ(y) ⊗_R M)`. -/
theorem finrank_fibre_eq_of_iso_tilde {R : CommRingCat.{u}} (G : (Spec R).Modules)
    (M : ModuleCat.{u} R) (hG : G ≅ (tilde.functor R).obj M) (y : Spec R) :
    finrank (ResidueField ((Spec R).presheaf.stalk y))
        (ResidueField ((Spec R).presheaf.stalk y) ⊗[(Spec R).presheaf.stalk y]
          G.presheaf.stalk y) =
      finrank y.asIdeal.ResidueField (y.asIdeal.ResidueField ⊗[R] M) := by
  have : IsIso (Scheme.Modules.fromTildeΓ (R := R) G) :=
    isIso_fromTildeΓ_iff.mpr ⟨M, ⟨hG.symm⟩⟩
  have hloc : IsLocalizing (modulesSpecToSheaf.obj G) :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mp this
  have := isLocalizedModule_germTopLinear G hloc y
  let e : Γ(G, ⊤) ≃ₗ[R] M :=
    (moduleSpecΓFunctor.mapIso hG ≪≫ (tilde.toTildeΓNatIso.app M).symm).toLinearEquiv
  -- `κ ⊗_{O} G_y` is the base change of `Γ(G, ⊤)` along `R → κ`.
  have hbc := (IsLocalizedModule.isBaseChange y.asIdeal.primeCompl ((Spec R).presheaf.stalk y)
      (germTopLinear G y)).comp
    (TensorProduct.isBaseChange ((Spec R).presheaf.stalk y) (G.presheaf.stalk y)
      (ResidueField ((Spec R).presheaf.stalk y)))
  have h1 : finrank (ResidueField ((Spec R).presheaf.stalk y))
      (ResidueField ((Spec R).presheaf.stalk y) ⊗[(Spec R).presheaf.stalk y]
        G.presheaf.stalk y) =
      finrank (ResidueField ((Spec R).presheaf.stalk y))
        (ResidueField ((Spec R).presheaf.stalk y) ⊗[R] Γ(G, ⊤)) :=
    hbc.equiv.symm.finrank_eq
  rw [h1]
  -- compare residue fields
  let O := (Spec R).presheaf.stalk y
  let κ := ResidueField O
  let eO : O ≃+* Localization.AtPrime y.asIdeal :=
    (IsLocalization.algEquiv y.asIdeal.primeCompl O (Localization.AtPrime y.asIdeal)).toRingEquiv
  let τ : κ ≃+* y.asIdeal.ResidueField := ResidueField.mapEquiv eO
  have hτ : ∀ r : R, τ (algebraMap R κ r) = algebraMap R y.asIdeal.ResidueField
      ((RingEquiv.refl R) r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R O κ, ResidueField.algebraMap_eq]
    change ResidueField.map (eO : O →+* Localization.AtPrime y.asIdeal) (residue O _) = _
    rw [ResidueField.map_residue, IsScalarTower.algebraMap_apply R (Localization.AtPrime y.asIdeal)
      y.asIdeal.ResidueField, ResidueField.algebraMap_eq]
    congr 1
    exact (IsLocalization.algEquiv y.asIdeal.primeCompl O _).commutes r
  have hrk := rank_tensorProduct_eq_of_ringEquiv (RingEquiv.refl R) τ hτ e.toAddEquiv
    (fun r m => e.map_smul r m)
  exact congrArg Cardinal.toNat hrk

/-- On affine opens `U ⊆ f⁻¹ V`, the fibre of `Ω_{X/Y}` at the point of `U` given by a prime
`q ⊂ B = Γ(X, U)` has the dimension of `κ(q) ⊗_B Ω_{B/A}`, `A = Γ(Y, V)`. -/
theorem finrank_fibre_relativeDifferentials_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens))
    (y : Spec Γ(X, (U : X.Opens))) :
    letI := (f.appLE V U h).hom.toAlgebra
    finrank (ResidueField (X.presheaf.stalk (U.2.fromSpec y)))
        (ResidueField (X.presheaf.stalk (U.2.fromSpec y)) ⊗[X.presheaf.stalk (U.2.fromSpec y)]
          (Scheme.relativeDifferentials f).presheaf.stalk (U.2.fromSpec y)) =
      finrank y.asIdeal.ResidueField
        (y.asIdeal.ResidueField ⊗[Γ(X, (U : X.Opens))]
          Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))]) := by
  let := (f.appLE V U h).hom.toAlgebra
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  rw [finrank_fibre_restrict U.2.fromSpec (Scheme.relativeDifferentials f) y]
  exact finrank_fibre_eq_of_iso_tilde _ _ (RelDiffLocal.affineIso f U V h) y

end

end Hartshorne
