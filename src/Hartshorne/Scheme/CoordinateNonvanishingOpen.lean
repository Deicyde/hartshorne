/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.MorphismFromGeneratedLineBundle

/-!
# Coordinate charts pull back to nonvanishing loci

Hartshorne, *Algebraic Geometry*, II, proof of Theorem 7.1 (pp. 150–151).

Let `Y` be a scheme (Hartshorne takes `Y = Spec A`), `X` a scheme, `L` an invertible sheaf on `X`
with global sections `s₀, …, sₙ`, and `φ : X ⟶ ℙⁿ_Y` a morphism with an isomorphism
`φ^* 𝒪(1) ≅ L` carrying each `φ^* xᵢ` to `sᵢ`; by Theorem 7.1 these properties characterize the
morphism defined by generating sections `sᵢ`. Then:

* `φ⁻¹(D₊(xᵢ)) = X_{sᵢ}`, the nonvanishing locus of `sᵢ`;
* on `X_{sᵢ}`, where `sᵢ` trivializes `L`, the function `φ^#(xⱼ/xᵢ)` is `sⱼ/sᵢ`, i.e.
  `sⱼ = φ^#(xⱼ/xᵢ) · sᵢ`;
* the restriction `X_{sᵢ} ⟶ D₊(xᵢ)` of the composite `X ⟶ ℙⁿ_Y ⟶ ℙⁿ_ℤ` is induced by the unique
  ring map `ℤ[x₀/xᵢ, …, xₙ/xᵢ] → Γ(X_{sᵢ}, 𝒪_X)` sending `xⱼ/xᵢ` to `sⱼ/sᵢ`. Since
  `ℙⁿ_Y = ℙⁿ_ℤ ×_ℤ Y`, this determines `φ` on `X_{sᵢ}` together with its composite to `Y`.

Here `D₊(xᵢ) ⊆ ℙⁿ_Y` is the preimage of the standard chart `D₊(xᵢ) ⊆ ℙⁿ_ℤ`, and `xⱼ/xᵢ` on it is
the pullback of the corresponding function on `ℙⁿ_ℤ`; on `D₊(xᵢ)` one has `xⱼ = (xⱼ/xᵢ) xᵢ` as
sections of `𝒪(1)`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  HomogeneousLocalization MvPolynomial

namespace Hartshorne

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The standard charts of `ℙⁿ_Y` -/

section Charts

variable (n : ℕ) (Y : Scheme.{u})

/-- The standard open `D₊(xᵢ)` of `ℙⁿ_Y = ℙⁿ_ℤ ×_ℤ Y`: the preimage of the chart `D₊(xᵢ)` of
`ℙⁿ_ℤ`. -/
def projectiveSpaceChart (i : Fin (n + 1)) : (projectiveSpaceOverScheme n Y).Opens :=
  toProjInt n Y ⁻¹ᵁ chartInt n i

/-- The function `xⱼ/xᵢ` on the standard open `D₊(xᵢ)` of `ℙⁿ_Y`, pulled back from `ℙⁿ_ℤ`. -/
def projectiveSpaceChartRatio (i j : Fin (n + 1)) :
    Γ(projectiveSpaceOverScheme n Y, projectiveSpaceChart n Y i) :=
  (toProjInt n Y).app (chartInt n i) (ratioInt n i j)

/-- On `D₊(xᵢ) ⊆ ℙⁿ_Y`, the coordinate sections of `𝒪(1)` satisfy `xⱼ = (xⱼ/xᵢ) xᵢ`. -/
theorem restrict_projectiveSpaceCoordinate_eq_smul (i j : Fin (n + 1)) :
    (projectiveSpaceTwistingSheaf n Y 1).presheaf.map
        (homOfLE (le_top : projectiveSpaceChart n Y i ≤ ⊤)).op (projectiveSpaceCoordinate n Y j) =
      projectiveSpaceChartRatio n Y i j •
        (projectiveSpaceTwistingSheaf n Y 1).presheaf.map
          (homOfLE (le_top : projectiveSpaceChart n Y i ≤ ⊤)).op
          (projectiveSpaceCoordinate n Y i) := by
  change ((Scheme.Modules.pullback (toProjInt n Y)).obj (twistInt n)).presheaf.map
      (homOfLE (le_top : toProjInt n Y ⁻¹ᵁ chartInt n i ≤ ⊤)).op
      (pullbackGlobalSection (toProjInt n Y) (coordInt n j)) =
    (toProjInt n Y).app (chartInt n i) (ratioInt n i j) •
      ((Scheme.Modules.pullback (toProjInt n Y)).obj (twistInt n)).presheaf.map
        (homOfLE (le_top : toProjInt n Y ⁻¹ᵁ chartInt n i ≤ ⊤)).op
        (pullbackGlobalSection (toProjInt n Y) (coordInt n i))
  rw [pullbackGlobalSection_restrict, pullbackGlobalSection_restrict, ← pullbackSection_smul]
  congr 1
  exact ProjTwistingSheaf.restrict_degreeOneSection_eq_smul
    (X_mem_homogeneousSubmodule_one _ i) (X_mem_homogeneousSubmodule_one _ j)

/-- On `D₊(xᵢ) ⊆ ℙⁿ_Y`, the coordinate section `xᵢ` trivializes `𝒪(1)`; so `xⱼ/xᵢ` is the unique
function with `xⱼ = (xⱼ/xᵢ) xᵢ` there. -/
theorem isTrivializingSection_projectiveSpaceChart (i : Fin (n + 1)) :
    IsTrivializingSection (projectiveSpaceTwistingSheaf n Y 1) (projectiveSpaceChart n Y i)
      ((projectiveSpaceTwistingSheaf n Y 1).presheaf.map
        (homOfLE (le_top : projectiveSpaceChart n Y i ≤ ⊤)).op
        (projectiveSpaceCoordinate n Y i)) := by
  change IsTrivializingSection ((Scheme.Modules.pullback (toProjInt n Y)).obj (twistInt n))
    (toProjInt n Y ⁻¹ᵁ chartInt n i)
    (((Scheme.Modules.pullback (toProjInt n Y)).obj (twistInt n)).presheaf.map
      (homOfLE (le_top : toProjInt n Y ⁻¹ᵁ chartInt n i ≤ ⊤)).op
      (pullbackGlobalSection (toProjInt n Y) (coordInt n i)))
  rw [pullbackGlobalSection_restrict]
  exact IsTrivializingSection.pullback (toProjInt n Y)
    (IsTrivializingSection.of_isLocalFrame (ι := PUnit.{u + 1})
      (ProjTwistingSheaf.isLocalFrame_degreeOneSection (X_mem_homogeneousSubmodule_one _ i)))

end Charts

/-! ### Preimages of the charts and the restricted morphisms -/

section Preimage

variable {n : ℕ} {X Y : Scheme.{u}} {L : X.Modules} (hL : L.IsInvertible)
  (s : Fin (n + 1) → Γ(L, ⊤)) (φ : X ⟶ projectiveSpaceOverScheme n Y)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n Y 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n Y i)) = s i)

include he in
/-- **The inverse image of `D₊(xᵢ)` is `X_{sᵢ}`** (Hartshorne II, proof of Theorem 7.1). For a
morphism `φ : X ⟶ ℙⁿ_Y` with an isomorphism `φ^* 𝒪(1) ≅ L` carrying each `φ^* xᵢ` to `sᵢ` (the
morphism defined by generating sections `sᵢ`), the preimage of the standard open `D₊(xᵢ)` is the
nonvanishing locus `X_{sᵢ}` of `sᵢ`. -/
theorem preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens (i : Fin (n + 1)) :
    φ ⁻¹ᵁ projectiveSpaceChart n Y i = nonvanishingLocusOpens hL (s i) :=
  chartPreimage_eq_locus hL s φ e he i

include he in
/-- **On `X_{sᵢ}`, `φ` pulls `xⱼ/xᵢ` back to `sⱼ/sᵢ`** (Hartshorne II, proof of Theorem 7.1).
With `φ`, `e` as above, the ring map `Γ(D₊(xᵢ), 𝒪) → Γ(X_{sᵢ}, 𝒪_X)` induced by `φ` sends `xⱼ/xᵢ`
to the function `g` with `sⱼ = g · sᵢ` on `X_{sᵢ}` (unique, since `sᵢ` trivializes `L` there). -/
theorem appLE_projectiveSpaceChartRatio_smul (i j : Fin (n + 1)) :
    φ.appLE (projectiveSpaceChart n Y i) (nonvanishingLocusOpens hL (s i))
        (preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i).ge
        (projectiveSpaceChartRatio n Y i j) •
      L.presheaf.map (homOfLE (le_top : nonvanishingLocusOpens hL (s i) ≤ ⊤)).op (s i) =
    L.presheaf.map (homOfLE (le_top : nonvanishingLocusOpens hL (s i) ≤ ⊤)).op (s j) := by
  have h := appLE_ratioInt_of_iso hL s φ e he i j
  rw [Scheme.Hom.comp_appLE] at h
  change φ.appLE (projectiveSpaceChart n Y i) (nonvanishingLocusOpens hL (s i)) _
    ((toProjInt n Y).app (chartInt n i) (ratioInt n i j)) • _ = _
  rw [show φ.appLE (projectiveSpaceChart n Y i) (nonvanishingLocusOpens hL (s i))
      (preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i).ge
      ((toProjInt n Y).app (chartInt n i) (ratioInt n i j)) = sectionRatio hL s i j from h]
  exact (sectionRatio_spec hL s i j).symm

include he in
/-- **The restricted morphism is induced by `xⱼ/xᵢ ↦ sⱼ/sᵢ`** (Hartshorne II, proof of
Theorem 7.1). With `φ`, `e` as above, there is a unique ring map
`F : ℤ[x₀, …, xₙ]_{(xᵢ)} = ℤ[x₀/xᵢ, …, xₙ/xᵢ] → Γ(X_{sᵢ}, 𝒪_X)` with `sⱼ = F(xⱼ/xᵢ) · sᵢ` on
`X_{sᵢ}` for all `j`, and the composite `X_{sᵢ} ⊆ X ⟶ ℙⁿ_Y ⟶ ℙⁿ_ℤ` is
`X_{sᵢ} ⟶ Spec Γ(X_{sᵢ}, 𝒪_X) ⟶ Spec ℤ[x₀/xᵢ, …, xₙ/xᵢ] ≅ D₊(xᵢ) ⊆ ℙⁿ_ℤ`, induced by `F`.
(Hartshorne takes the base `Spec A`, where `D₊(xᵢ) ⊆ ℙⁿ_A` is `Spec A[x₀/xᵢ, …, xₙ/xᵢ]`; since
`ℙⁿ_Y = ℙⁿ_ℤ ×_ℤ Y`, this statement and the composite `X_{sᵢ} ⟶ Y` determine `φ` on `X_{sᵢ}`.) -/
theorem existsUnique_chartRingHom_of_iso (i : Fin (n + 1)) :
    ∃! F : CommRingCat.of (Away (GeneratedProj.intGrading.{u} n) (MvPolynomial.X i)) ⟶
        Γ(X, nonvanishingLocusOpens hL (s i)),
      (∀ j, F.hom (chartRatio (ULift.{u} ℤ) i j) •
          L.presheaf.map (homOfLE (le_top : nonvanishingLocusOpens hL (s i) ≤ ⊤)).op (s i) =
        L.presheaf.map (homOfLE (le_top : nonvanishingLocusOpens hL (s i) ≤ ⊤)).op (s j)) ∧
      (nonvanishingLocusOpens hL (s i)).ι ≫ φ ≫ toProjInt n Y =
        (nonvanishingLocusOpens hL (s i)).toSpecΓ ≫ Spec.map F ≫
          Proj.awayι _ (MvPolynomial.X i) (X_mem_homogeneousSubmodule_one _ i) Nat.one_pos := by
  have hle : nonvanishingLocusOpens hL (s i) ≤ (φ ≫ toProjInt n Y) ⁻¹ᵁ chartInt n i :=
    (chartPreimage_eq_locus hL s φ e he i).ge
  refine ⟨Proj.awayToSection _ (MvPolynomial.X i) ≫ (φ ≫ toProjInt n Y).appLE (chartInt n i)
    (nonvanishingLocusOpens hL (s i)) hle, ⟨fun j => ?_, ?_⟩, ?_⟩
  · have h := appLE_ratioInt_of_iso hL s φ e he i j
    change (φ ≫ toProjInt n Y).appLE (chartInt n i) (nonvanishingLocusOpens hL (s i)) hle
      (ratioInt n i j) • _ = _
    rw [h]
    exact (sectionRatio_spec hL s i j).symm
  · exact ι_comp_eq_toSpecΓ_SpecMap (φ ≫ toProjInt n Y) (nonvanishingLocusOpens hL (s i))
      (X_mem_homogeneousSubmodule_one _ i) Nat.one_pos hle
  · rintro F ⟨hF, -⟩
    ext1
    refine chart_ringHom_ext i (fun r => ?_) (fun j => ?_)
    · exact congrArg (fun G : ULift.{u} ℤ →+* Γ(X, nonvanishingLocusOpens hL (s i)) => G r)
        (ulift_int_ringHom_ext (F.hom.comp (chartConst (ULift.{u} ℤ) i))
          ((Proj.awayToSection _ (MvPolynomial.X i) ≫ (φ ≫ toProjInt n Y).appLE (chartInt n i)
            (nonvanishingLocusOpens hL (s i)) hle).hom.comp (chartConst (ULift.{u} ℤ) i)))
    · refine eq_of_smul_eq hL s i le_rfl ?_
      rw [hF j]
      have h := appLE_ratioInt_of_iso hL s φ e he i j
      change _ = (φ ≫ toProjInt n Y).appLE (chartInt n i) (nonvanishingLocusOpens hL (s i)) hle
        (ratioInt n i j) • _
      rw [h]
      exact sectionRatio_spec hL s i j

end Preimage

end Hartshorne
