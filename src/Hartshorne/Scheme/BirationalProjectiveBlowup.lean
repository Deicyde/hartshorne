/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BirationalBlowupRees

/-!
# A birational projective morphism is a blowup

Hartshorne, *Algebraic Geometry*, II, Theorem 7.17 (pp. 166–168).
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne.BirationalBlowup

open SectionAlgebraModel Scheme QuasiCoherentGradedAlgebra

/-! ### Gluing the local identifications -/

namespace Setup

variable {r : ℕ} {X Z : Scheme.{u}} {i : Z ⟶ projectiveSpaceOverScheme r X} [IsIntegral X]
  [IsIntegral Z] [IsNoetherian X] {d : ℕ} (P : Setup i d)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem isEmpty_proj (A : QuasiCoherentGradedAlgebra X) (U : X.AffineZariskiSite)
    (hU : genericPoint X ∉ U.1) : IsEmpty (Proj (A.grading U)) := by
  have h := opens_eq_bot_of_genericPoint_notMem hU
  refine ⟨fun x => ?_⟩
  obtain ⟨z, hz⟩ := (A.projToOpen U).base x
  have hz' : z ∈ U.1 := hz
  rw [h] at hz'
  exact hz'

open Classical in
/-- The local isomorphism `Proj (⊕_m I(U)ᵐ) ≅ Proj (S · D)(U)` over an affine open `U` on which `D`
has a frame: the identification `S(U) ≅ ⊕_m I(U)ᵐ` followed by the inverse of the local
isomorphism of Lemma 7.9 (both schemes are empty when `U` is). -/
def localIso (U : (framedAffines P.D).FullSubcategory) :
    Proj (P.I.reesAlgebra.grading U.obj) ≅ Proj ((P.S.lineBundleTwist P.D P.hD).grading U.obj) :=
  if hU : genericPoint X ∈ U.obj.1 then
    projIsoOfBijective (P.ρ U.obj hU U.property.choose_spec)
        (P.ρ_bijective U.obj hU U.property.choose_spec) ≪≫
      (P.S.framedIso (hL := P.hD) U).symm
  else
    have := isEmpty_proj P.I.reesAlgebra U.obj hU
    have := isEmpty_proj (P.S.lineBundleTwist P.D P.hD) U.obj hU
    isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty

theorem localIso_hom_of_mem (U : (framedAffines P.D).FullSubcategory)
    (hU : genericPoint X ∈ U.obj.1) :
    (P.localIso U).hom = (projIsoOfBijective (P.ρ U.obj hU U.property.choose_spec)
        (P.ρ_bijective U.obj hU U.property.choose_spec)).hom ≫
      (P.S.framedIso (hL := P.hD) U).inv := by
  rw [localIso, dif_pos hU]
  rfl

private theorem projMap_congr' {A B : Type u} [CommRing A] [CommRing B] {𝒜 : ℕ → AddSubgroup A}
    {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ] {φ ψ : 𝒜 →+*ᵍ ℬ} (e : φ = ψ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ) :
    Proj.map φ hφ = Proj.map ψ hψ := by
  subst e
  rfl

theorem localIso_naturality {U V : (framedAffines P.D).FullSubcategory} (f : U ⟶ V) :
    Proj.map (P.I.reesAlgebra.restrict f.hom) (P.I.reesAlgebra.irrelevant_le f.hom) ≫
        (P.localIso V).hom =
      (P.localIso U).hom ≫ Proj.map ((P.S.lineBundleTwist P.D P.hD).restrict f.hom)
        ((P.S.lineBundleTwist P.D P.hD).irrelevant_le f.hom) := by
  by_cases hU : genericPoint X ∈ U.obj.1
  swap
  · have := isEmpty_proj P.I.reesAlgebra U.obj hU
    exact isInitialOfIsEmpty.hom_ext _ _
  have hV : genericPoint X ∈ V.obj.1 := AffineZariskiSite.toOpens_mono f.hom.le hU
  have hpU := U.property.choose_spec
  have hpV := V.property.choose_spec
  have hpVU := isLocalFrame_restrictFrame f.hom hpV
  rw [localIso_hom_of_mem P U hU, localIso_hom_of_mem P V hV,
    P.projIso_ρ_eq U.obj hU hpVU hpU]
  have key : Proj.map (P.I.reesAlgebra.restrict f.hom) (P.I.reesAlgebra.irrelevant_le f.hom) ≫
      (projIsoOfBijective (P.ρ V.obj hV hpV) (P.ρ_bijective V.obj hV hpV)).hom =
      (projIsoOfBijective (P.ρ U.obj hU hpVU) (P.ρ_bijective U.obj hU hpVU)).hom ≫
        Proj.map (P.S.restrict f.hom) (P.S.irrelevant_le f.hom) := by
    rw [projIsoOfBijective_hom, projIsoOfBijective_hom, ← Proj.map_comp, ← Proj.map_comp]
    exact projMap_congr' (P.ρ_restrict f.hom hU hpV) _ _
  have key2 : (P.S.framedIso (hL := P.hD) U).inv ≫
      Proj.map ((P.S.lineBundleTwist P.D P.hD).restrict f.hom)
        ((P.S.lineBundleTwist P.D P.hD).irrelevant_le f.hom) =
      Proj.map (P.S.restrict f.hom) (P.S.irrelevant_le f.hom) ≫
        (P.S.framedIso (hL := P.hD) V).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← framedIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, key, Category.assoc, Category.assoc, key2]

theorem localIso_hom_toSpec (U : (framedAffines P.D).FullSubcategory) :
    (P.localIso U).hom ≫ Proj.toSpecZero ((P.S.lineBundleTwist P.D P.hD).grading U.obj) ≫
        Spec.map ((P.S.lineBundleTwist P.D P.hD).toZero U.obj) =
      Proj.toSpecZero (P.I.reesAlgebra.grading U.obj) ≫ Spec.map (P.I.reesAlgebra.toZero U.obj) := by
  by_cases hU : genericPoint X ∈ U.obj.1
  swap
  · have := isEmpty_proj P.I.reesAlgebra U.obj hU
    exact isInitialOfIsEmpty.hom_ext _ _
  rw [localIso_hom_of_mem P U hU, Category.assoc, ← P.S.framedIso_hom_toSpec (hL := P.hD) U,
    Iso.inv_hom_id_assoc, projIsoOfBijective_hom, ← Category.assoc, projMap_toSpecZero,
    Category.assoc, ← Spec.map_comp]
  congr 2
  ext a : 2
  exact Subtype.ext (P.ρ_structureMap U.obj hU U.property.choose_spec a)

/-- **`Bl_I X ≅ Proj_X S` over `X`** (Hartshorne II, proof of Theorem 7.17, Step 5): the local
identifications `S(U) ≅ ⊕_m I(U)ᵐ` glue, through Lemma 7.9 for `S · D`, to an isomorphism
`Proj_X (⊕_m Iᵐ) ≅ Proj_X (S · D) ≅ Proj_X S`. -/
def blowupIso : P.I.reesAlgebra.relProj ≅ P.S.relProj :=
  framedGlueIso P.hD P.localIso P.localIso_naturality ≪≫ P.S.lineBundleTwistIso P.hD

theorem blowupIso_hom_relProjToBase :
    P.blowupIso.hom ≫ P.S.relProjToBase = P.I.reesAlgebra.relProjToBase := by
  rw [blowupIso, Iso.trans_hom, Category.assoc, lineBundleTwistIso_hom_relProjToBase,
    framedGlueIso_hom_relProjToBase _ _ _ P.localIso_hom_toSpec]

end Setup

end Hartshorne.BirationalBlowup
