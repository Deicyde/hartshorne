/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.CanonicalSheafProjectiveSpace
import Hartshorne.Scheme.Differentials.TangentSheaf
import Hartshorne.RingedSpace.ModuleSheafDualExact

/-!
# The tangent sequence of projective space

Hartshorne, *Algebraic Geometry*, II.8, Example 8.20.1 (p. 182): taking the dual of the Euler
sequence `0 → Ω → 𝒪(-1)^{n+1} → 𝒪 → 0` of (8.13) gives the exact sequence

`0 → 𝒪_X → 𝒪_X(1)^{n+1} → T_X → 0`

on `X = ℙⁿ_k`.

* `Hartshorne.EulerSequence.dualEulerSequence_shortExact`: the dual of the Euler sequence is short
  exact (`Hartshorne.Ringed.dualShortComplex_shortExact`, since `𝒪_X` is locally free).
* `Hartshorne.EulerSequence.nonempty_dual_O0_iso`, `Hartshorne.EulerSequence.nonempty_dual_O1_iso`:
  `𝒪^∨ ≅ 𝒪` and `𝒪(-1)^∨ ≅ 𝒪(1)`, computed in the Picard group.
* `Hartshorne.EulerSequence.tangentSequence_projectiveSpace`: the tangent sequence.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Hartshorne.EulerSequence

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {k : Type u} [Field k] {n : ℕ}

/-- An isomorphism of `𝒪_X`-modules, as an isomorphism of sheaves of modules over the structure
sheaf. -/
def ringedIsoOfModules {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    Iso (C := SheafOfModules.{u} (ringCatSheafOf X.sheaf)) M N :=
  ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- **The dual of the Euler sequence is short exact:**
`0 → 𝒪^∨ → (𝒪(-1)^{n+1})^∨ → Ω^∨ = T_X → 0` on `ℙⁿ_k`. -/
theorem dualEulerSequence_shortExact :
    (Ringed.dualShortComplex (R := (Proj (grading k n)).sheaf)
      (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)).ShortExact :=
  Ringed.dualShortComplex_shortExact (eulerSequence k n).1
    (Ringed.structureModule_isInvertible (R := (Proj (grading k n)).sheaf)).isFiniteLocallyFree

/-- `𝒪^∨ ≅ 𝒪` on `ℙⁿ_k`. -/
theorem nonempty_dual_O0_iso :
    Nonempty (Ringed.moduleSheafDual (R := (Proj (grading k n)).sheaf) (O0 k n) ≅ O0 k n) := by
  let _ : CommGroup (Ringed.Pic (Proj (grading k n)).sheaf) := Ringed.Pic.instCommGroup
  have hO := Ringed.structureModule_isInvertible (R := (Proj (grading k n)).sheaf)
  have h : Ringed.Pic.mk _ (Ringed.isInvertible_moduleSheafDual hO) = Ringed.Pic.mk _ hO :=
    calc Ringed.Pic.mk _ (Ringed.isInvertible_moduleSheafDual hO)
        = (Ringed.Pic.mk _ hO)⁻¹ := (Ringed.Pic.inv_mk hO).symm
      _ = 1 := (congrArg Inv.inv Ringed.Pic.one_eq_mk.symm).trans inv_one
      _ = Ringed.Pic.mk _ hO := Ringed.Pic.one_eq_mk
  obtain ⟨e⟩ := (Ringed.Pic.mk_eq_mk_iff _ _).mp h
  exact ⟨modulesIsoOfRinged e⟩

/-- `𝒪(-1)^∨ ≅ 𝒪(1)` on `ℙⁿ_k`. -/
theorem nonempty_dual_O1_iso :
    Nonempty (Ringed.moduleSheafDual (R := (Proj (grading k n)).sheaf) (O1 k n) ≅
      projTwistingSheaf (grading k n) 1) := by
  let _ : CommGroup (Ringed.Pic (Proj (grading k n)).sheaf) := Ringed.Pic.instCommGroup
  have hm : ∀ l : ℤ, Ringed.IsInvertible (R := (Proj (grading k n)).sheaf)
      (projTwistingSheaf (grading k n) l) := fun l ↦
    (Scheme.Modules.isLocallyFreeOfRank_iff_ringed _ _).1
      (ProjectiveSpacePicard.projTwistingSheaf_isInvertible l)
  have hmul : ∀ a b : ℤ, Ringed.Pic.mk _ (hm a) * Ringed.Pic.mk _ (hm b) =
      Ringed.Pic.mk _ (hm (a + b)) := fun a b ↦
    (Ringed.Pic.mk_mul_mk _ _).trans ((Ringed.Pic.mk_eq_mk_iff _ _).mpr
      ⟨Ringed.moduleSheafTensorIsoTensor _ _ ≪≫ ringedIsoOfModules
        (twistMulIso (grading k n) (ProjectiveSpacePicard.adjoin_one_eq_top k n) a b)⟩)
  have hcongr : ∀ a b : ℤ, a = b → Ringed.Pic.mk _ (hm a) = Ringed.Pic.mk _ (hm b) := by
    rintro a _ rfl
    rfl
  have h0 : Ringed.Pic.mk _ (hm 0) = 1 :=
    mul_eq_left.mp ((hmul 1 0).trans (hcongr _ _ (add_zero 1)))
  have h1 : Ringed.Pic.mk _ (hm 1) = (Ringed.Pic.mk _ (hm (-1)))⁻¹ :=
    eq_inv_of_mul_eq_one_left ((hmul 1 (-1)).trans ((hcongr _ _ (add_neg_cancel 1)).trans h0))
  obtain ⟨e⟩ := (Ringed.Pic.mk_eq_mk_iff _ _).mp (h1.trans (Ringed.Pic.inv_mk _))
  exact ⟨modulesIsoOfRinged e.symm⟩

variable (k n) in
/-- The dual of the Euler sequence, `𝒪^∨ → (𝒪(-1)^{n+1})^∨ → T_X`, as a short complex of
`𝒪_X`-modules. -/
noncomputable def dualEulerComplex : ShortComplex (Proj (grading k n)).Modules where
  X₁ := Ringed.moduleSheafDual (R := (Proj (grading k n)).sheaf) (O0 k n)
  X₂ := Ringed.moduleSheafDual (R := (Proj (grading k n)).sheaf) (E k n)
  X₃ := tangentSheaf (toBase k n)
  f := (Ringed.dualShortComplex (R := (Proj (grading k n)).sheaf)
    (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)).f
  g := (Ringed.dualShortComplex (R := (Proj (grading k n)).sheaf)
    (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)).g
  zero := (Ringed.dualShortComplex (R := (Proj (grading k n)).sheaf)
    (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)).zero

theorem dualEulerComplex_shortExact : (dualEulerComplex k n).ShortExact :=
  dualEulerSequence_shortExact

/-- `(𝒪(-1)^{n+1})^∨ ≅ 𝒪(1)^{n+1}` on `ℙⁿ_k`. -/
theorem nonempty_dual_E_iso :
    Nonempty ((dualEulerComplex k n).X₂ ≅
      ⨁ fun _ : Fin (n + 1) ↦ projTwistingSheaf (grading k n) 1) := by
  obtain ⟨e₁⟩ := nonempty_dual_O1_iso (k := k) (n := n)
  let L : (Proj (grading k n)).Modules :=
    Ringed.moduleSheafDual (R := (Proj (grading k n)).sheaf) (O1 k n)
  let e₁' : L ≅ projTwistingSheaf (grading k n) 1 := e₁
  exact ⟨modulesIsoOfRinged (Ringed.moduleSheafHomBiproductIso (R := (Proj (grading k n)).sheaf)
        (fun _ : Fin (n + 1) ↦ O1 k n) (O0 k n)
        (hF := (inferInstance : HasBiproduct fun _ : Fin (n + 1) ↦ O1 k n))
        (hG := (inferInstance : HasBiproduct fun _ : Fin (n + 1) ↦ L))) ≪≫
      biproduct.mapIso (f := fun _ : Fin (n + 1) ↦ L) fun _ ↦ e₁'⟩

/-- **Hartshorne II.8, Example 8.20.1 (the tangent sequence).** On `X = ℙⁿ_k` there is an exact
sequence `0 → 𝒪_X → 𝒪_X(1)^{n+1} → T_X → 0`, obtained by dualizing the Euler sequence (8.13): the
maps are those of `Hartshorne.EulerSequence.dualEulerSequence_shortExact` composed with the
identifications `𝒪^∨ ≅ 𝒪` and `(𝒪(-1)^{n+1})^∨ ≅ 𝒪(1)^{n+1}`. -/
theorem tangentSequence_projectiveSpace :
    ∃ (a : O0 k n ⟶ ⨁ fun _ : Fin (n + 1) ↦ projTwistingSheaf (grading k n) 1)
      (b : (⨁ fun _ : Fin (n + 1) ↦ projTwistingSheaf (grading k n) 1) ⟶
        tangentSheaf (toBase k n))
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  obtain ⟨e₀⟩ := nonempty_dual_O0_iso (k := k) (n := n)
  obtain ⟨eE⟩ := nonempty_dual_E_iso (k := k) (n := n)
  let D := dualEulerComplex k n
  let e₀' : D.X₁ ≅ O0 k n := e₀
  refine ⟨e₀'.inv ≫ D.f ≫ eE.hom, eE.inv ≫ D.g, by simp, ?_⟩
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk e₀' eE (Iso.refl D.X₃) (by simp) (by simp)) dualEulerComplex_shortExact

end Hartshorne.EulerSequence
