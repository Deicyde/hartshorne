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
* `Hartshorne.EulerSequence.nonempty_dual_E_iso`: `(𝒪(-1)^{n+1})^∨ ≅ 𝒪(1)^{n+1}`.
* `Hartshorne.EulerSequence.tangentSequence_projectiveSpace_iso`: the dual of the Euler sequence is
  short exact, with terms `≅ 𝒪`, `≅ 𝒪(1)^{n+1}` and `= T_X`.
* `Hartshorne.EulerSequence.tangentSequence_projectiveSpace`: the tangent sequence, as the short
  exact sequence `0 → 𝒪^∨ → (𝒪(-1)^{n+1})^∨ → T_X → 0`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Hartshorne.EulerSequence

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/- Use the preadditive structure coming from the abelian structure, as the sheaf-`Ext` API used by
`Hartshorne.RingedSpace.ModuleSheafDualExact` does. -/
attribute [local instance 2000] Abelian.toPreadditive

variable {k : Type u} [Field k] {n : ℕ}

/-- An isomorphism of `𝒪_X`-modules, as an isomorphism of sheaves of modules over the structure
sheaf. -/
def ringedIsoOfModules {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    Iso (C := SheafOfModules.{u} (ringCatSheafOf X.sheaf)) M N :=
  ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- A short complex of sheaves of modules over the structure sheaf, as a short complex of
`𝒪_X`-modules. -/
noncomputable def shortComplexToModules {X : Scheme.{u}}
    (S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf X.sheaf))) : ShortComplex X.Modules :=
  ShortComplex.mk (C := X.Modules) S.f S.g S.zero

/-- `Hartshorne.EulerSequence.shortComplexToModules` preserves short exactness. -/
theorem shortComplexToModules_shortExact {X : Scheme.{u}}
    {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf X.sheaf))} (hS : S.ShortExact) :
    (shortComplexToModules S).ShortExact :=
  hS

/-- The dual `ℋom(F, 𝒪_X)` of an `𝒪_X`-module. -/
noncomputable abbrev dualModules {X : Scheme.{u}} (F : X.Modules) : X.Modules :=
  Ringed.moduleSheafDual (R := X.sheaf) F

/-- The dual of a finite direct sum of `𝒪_X`-modules is the direct sum of the duals. -/
noncomputable def dualModulesBiproductIso {X : Scheme.{u}} {ι : Type} [Fintype ι]
    (F : ι → X.Modules) : dualModules (⨁ F) ≅ ⨁ fun i ↦ dualModules (F i) :=
  modulesIsoOfRinged (Ringed.moduleSheafHomBiproductIso (R := X.sheaf) F
    (Ringed.structureModule X.sheaf)
    (hF := (inferInstance : HasBiproduct F))
    (hG := (inferInstance : HasBiproduct fun i ↦ dualModules (F i))))

/-- The dual `0 ⟶ F''^∨ ⟶ F^∨ ⟶ F'^∨ ⟶ 0` of a short complex `F' ⟶ F ⟶ F''` of `𝒪_X`-modules. -/
noncomputable def dualModulesComplex {X : Scheme.{u}} (S : ShortComplex X.Modules) :
    ShortComplex X.Modules :=
  shortComplexToModules (Ringed.dualShortComplex (R := X.sheaf)
    (ShortComplex.mk (C := SheafOfModules.{u} (ringCatSheafOf X.sheaf)) S.f S.g S.zero))

/-- **Dualizing a short exact sequence of `𝒪_X`-modules** whose last term is locally free of
finite rank gives a short exact sequence. -/
theorem dualModulesComplex_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h₃ : Ringed.IsFiniteLocallyFree (R := X.sheaf) S.X₃) :
    (dualModulesComplex S).ShortExact :=
  shortComplexToModules_shortExact (Ringed.dualShortComplex_shortExact hS h₃)

/-- The structure sheaf is locally free of finite rank. -/
theorem isFiniteLocallyFree_unit (X : Scheme.{u}) :
    Ringed.IsFiniteLocallyFree (R := X.sheaf) (SheafOfModules.unit X.ringCatSheaf) :=
  (Ringed.structureModule_isInvertible (R := X.sheaf)).isFiniteLocallyFree

/-- If `0 ⟶ Ω_{X/k} ⟶ F ⟶ F'' ⟶ 0` is short exact with `F''` locally free of finite rank, and
`F''^∨ ≅ A`, `F^∨ ≅ B`, then there is a short exact sequence `0 ⟶ A ⟶ B ⟶ T_X ⟶ 0`. -/
theorem exists_shortExact_tangentSheaf_of_dual {X : Scheme.{u}} {k : Type u} [Field k]
    (φ : X ⟶ Spec (.of k)) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₃ : Ringed.IsFiniteLocallyFree (R := X.sheaf) S.X₃)
    (hΩ : S.X₁ = Scheme.relativeDifferentials φ) {A B : X.Modules}
    (e₀ : dualModules S.X₃ ≅ A) (eE : dualModules S.X₂ ≅ B) :
    ∃ (a : A ⟶ B) (b : B ⟶ tangentSheaf φ) (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  have hD := dualModulesComplex_shortExact hS h₃
  let D := dualModulesComplex S
  let e₀' : D.X₁ ≅ A := e₀
  let eE' : D.X₂ ≅ B := eE
  let e₃ : D.X₃ ≅ tangentSheaf φ := eqToIso (congrArg dualModules hΩ)
  refine ⟨e₀'.inv ≫ D.f ≫ eE'.hom, eE'.inv ≫ D.g ≫ e₃.hom, ?_, ?_⟩
  · simp only [Category.assoc, Iso.hom_inv_id_assoc, ShortComplex.zero_assoc, zero_comp,
      comp_zero]
  · exact ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk e₀' eE' e₃ (by simp) (by simp)) hD

/-- **The dual of the Euler sequence is short exact:**
`0 → 𝒪^∨ → (𝒪(-1)^{n+1})^∨ → Ω^∨ = T_X → 0` on `ℙⁿ_k`. -/
theorem dualEulerSequence_shortExact :
    (Ringed.dualShortComplex (R := (Proj (grading k n)).sheaf)
      (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)).ShortExact :=
  Ringed.dualShortComplex_shortExact (eulerSequence k n).1
    (Ringed.structureModule_isInvertible (R := (Proj (grading k n)).sheaf)).isFiniteLocallyFree

/-- `𝒪^∨ ≅ 𝒪` on `ℙⁿ_k`. -/
theorem nonempty_dual_O0_iso :
    Nonempty (dualModules (O0 k n) ≅ O0 k n) := by
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
    Nonempty (dualModules (O1 k n) ≅ projTwistingSheaf (grading k n) 1) := by
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
/-- The dual `𝒪^∨ → (𝒪(-1)^{n+1})^∨ → T_X` of the Euler sequence, as a short complex of
`𝒪_X`-modules. -/
noncomputable def dualEulerComplex : ShortComplex (Proj (grading k n)).Modules :=
  dualModulesComplex (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)

/-- The dual of the Euler sequence (8.13) is short exact, since `𝒪_X` is locally free of finite
rank. -/
theorem dualEulerComplex_shortExact : (dualEulerComplex k n).ShortExact :=
  dualModulesComplex_shortExact (eulerSequence k n).1 (isFiniteLocallyFree_unit _)

/-- **Hartshorne II.8, Example 8.20.1 (the tangent sequence).** On `X = ℙⁿ_k`, dualizing the
Euler sequence (8.13) `0 → Ω → 𝒪(-1)^{n+1} → 𝒪 → 0` gives a short exact sequence
`0 → 𝒪^∨ → (𝒪(-1)^{n+1})^∨ → T_X → 0`. Together with `𝒪^∨ ≅ 𝒪`
(`Hartshorne.EulerSequence.nonempty_dual_O0_iso`) and `(𝒪(-1)^{n+1})^∨ ≅ 𝒪(1)^{n+1}`
(`Hartshorne.EulerSequence.nonempty_dual_E_iso`) this is the exact sequence
`0 → 𝒪_X → 𝒪_X(1)^{n+1} → T_X → 0`. -/
theorem tangentSequence_projectiveSpace :
    ∃ (a : dualModules (O0 k n) ⟶ dualModules (⨁ fun _ : Fin (n + 1) ↦ O1 k n))
      (b : dualModules (⨁ fun _ : Fin (n + 1) ↦ O1 k n) ⟶ tangentSheaf (toBase k n))
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact :=
  exists_shortExact_tangentSheaf_of_dual (toBase k n) (eulerSequence k n).1
    (isFiniteLocallyFree_unit _) rfl (Iso.refl _) (Iso.refl _)

/-- `(𝒪(-1)^{n+1})^∨ ≅ 𝒪(1)^{n+1}` on `ℙⁿ_k`. -/
theorem nonempty_dual_E_iso :
    Nonempty (dualModules (⨁ fun _ : Fin (n + 1) ↦ O1 k n) ≅
      ⨁ fun _ : Fin (n + 1) ↦ projTwistingSheaf (grading k n) 1) := by
  obtain ⟨e₁⟩ := nonempty_dual_O1_iso (k := k) (n := n)
  exact ⟨dualModulesBiproductIso (fun _ : Fin (n + 1) ↦ O1 k n) ≪≫
    biproduct.mapIso (f := fun _ : Fin (n + 1) ↦ dualModules (O1 k n)) fun _ ↦ e₁⟩

/-- Hartshorne II.8, Example 8.20.1: the dual of the Euler sequence (8.13) is a short exact
sequence `0 → 𝒪 → 𝒪(1)^{n+1} → T_X → 0`: its terms are `≅ 𝒪`, `≅ 𝒪(1)^{n+1}` and `= T_X`. -/
theorem tangentSequence_projectiveSpace_iso :
    (dualModulesComplex (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)).ShortExact ∧
    Nonempty ((dualModulesComplex (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)).X₁ ≅
      O0 k n) ∧
    Nonempty ((dualModulesComplex (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)).X₂ ≅
      ⨁ fun _ : Fin (n + 1) ↦ projTwistingSheaf (grading k n) 1) ∧
    (dualModulesComplex (ShortComplex.mk (alpha k n) (beta k n) alpha_beta)).X₃ =
      tangentSheaf (toBase k n) :=
  ⟨dualEulerComplex_shortExact, nonempty_dual_O0_iso, nonempty_dual_E_iso, rfl⟩

/-- The last term of `Hartshorne.EulerSequence.dualEulerComplex` is the tangent sheaf. -/
theorem dualEulerComplex_X₃ : (dualEulerComplex k n).X₃ = tangentSheaf (toBase k n) :=
  rfl

end Hartshorne.EulerSequence
