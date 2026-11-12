/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeProj
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Morphisms out of a relative Proj

Hartshorne, *Algebraic Geometry*, II.7, p. 160: `Proj_X S` is glued from the schemes
`Proj S(U)` over the affine opens `U ⊆ X`. A family of morphisms `Proj S(U) ⟶ W` compatible with
the restrictions of `S` therefore induces a morphism `Proj_X S ⟶ W`
(`QuasiCoherentGradedAlgebra.relProjDesc`). If `W` lies over `X` by `g : W ⟶ X`, each
`Proj S(U) ⟶ W` is an open immersion over `U` with image `g⁻¹(U)`, then the induced morphism is an
isomorphism over `X` (`QuasiCoherentGradedAlgebra.isIso_relProjDesc`). This is the gluing step
used to identify a relative Proj with a given scheme, as in the proof of Hartshorne II,
Theorem 7.17, Step 3.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Hartshorne

namespace QuasiCoherentGradedAlgebra

variable {X : Scheme.{u}} (S : QuasiCoherentGradedAlgebra X)

instance : (S.relativeGluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

variable {W : Scheme.{u}}
  (j : ∀ U : X.AffineZariskiSite, Proj (S.grading U) ⟶ W)
  (hmap : ∀ {U V : X.AffineZariskiSite} (i : U ⟶ V),
    Proj.map (S.restrict i) (S.irrelevant_le i) ≫ j V = j U)

/-- Morphisms `Proj S(U) ⟶ W` compatible with the restrictions of `S` form a cocone over the
gluing diagram of `Proj_X S`. -/
def coconeOfProj : Cocone S.relativeGluingData.functor where
  pt := W
  ι :=
    { app U := j U
      naturality _ _ i := (hmap i).trans (Category.comp_id _).symm }

/-- The morphism `Proj_X S ⟶ W` induced by compatible morphisms `j U : Proj S(U) ⟶ W`. -/
def relProjDesc : S.relProj ⟶ W :=
  colimit.desc _ (S.coconeOfProj j hmap)

@[reassoc (attr := simp)]
theorem projι_relProjDesc (U : X.AffineZariskiSite) : S.projι U ≫ S.relProjDesc j hmap = j U :=
  colimit.ι_desc _ _

theorem relProjDesc_unique (φ : S.relProj ⟶ W) (hφ : ∀ U, S.projι U ≫ φ = j U) :
    φ = S.relProjDesc j hmap :=
  colimit.hom_ext fun U => (hφ U).trans (S.projι_relProjDesc j hmap U).symm

variable (g : W ⟶ X)

@[reassoc]
theorem relProjDesc_comp (hbase : ∀ U : X.AffineZariskiSite, j U ≫ g = S.projToOpen U ≫ U.1.ι) :
    S.relProjDesc j hmap ≫ g = S.relProjToBase :=
  colimit.hom_ext fun U => by
    change S.projι U ≫ S.relProjDesc j hmap ≫ g = S.projι U ≫ S.relProjToBase
    rw [projι_relProjDesc_assoc, hbase, projι_relProjToBase]

/-- **Identifying a relative Proj.** If `g : W ⟶ X` and the compatible morphisms
`j U : Proj S(U) ⟶ W` are open immersions over `U` with image `g⁻¹(U)`, then the induced morphism
`Proj_X S ⟶ W` is an isomorphism. -/
theorem isIso_relProjDesc [∀ U, IsOpenImmersion (j U)]
    (hbase : ∀ U : X.AffineZariskiSite, j U ≫ g = S.projToOpen U ≫ U.1.ι)
    (hrange : ∀ U : X.AffineZariskiSite, g ⁻¹ᵁ U.1 = (j U).opensRange) :
    IsIso (S.relProjDesc j hmap) := by
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _)
    (fun U : X.affineOpens => g ⁻¹ᵁ U.1)
    (by rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top])]
  intro U
  let V : X.AffineZariskiSite := ⟨U.1, U.2⟩
  have hpre : S.relProjDesc j hmap ⁻¹ᵁ g ⁻¹ᵁ U.1 = (S.projι V).opensRange := by
    rw [← Scheme.Hom.comp_preimage, S.relProjDesc_comp j hmap g hbase, S.relProjToBase_preimage V]
  let e := IsOpenImmersion.isoOfRangeEq (S.projι V) (S.relProjDesc j hmap ⁻¹ᵁ g ⁻¹ᵁ U.1).ι
    (by rw [Scheme.Opens.range_ι, hpre, Scheme.Hom.coe_opensRange])
  let e' := IsOpenImmersion.isoOfRangeEq (j V) (g ⁻¹ᵁ U.1).ι
    (by
      rw [Scheme.Opens.range_ι]
      exact ((congrArg SetLike.coe (hrange V)).trans (Scheme.Hom.coe_opensRange _)).symm)
  have key : e.hom ≫ S.relProjDesc j hmap ∣_ (g ⁻¹ᵁ U.1) = e'.hom := by
    rw [← cancel_mono (g ⁻¹ᵁ U.1).ι, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, projι_relProjDesc,
      IsOpenImmersion.isoOfRangeEq_hom_fac]
  have : S.relProjDesc j hmap ∣_ (g ⁻¹ᵁ U.1) = e.inv ≫ e'.hom := by
    rw [← key, Iso.inv_hom_id_assoc]
  rw [MorphismProperty.isomorphisms.iff, this]
  infer_instance

/-- The isomorphism `Proj_X S ≅ W` over `X` induced by compatible open immersions
`Proj S(U) ⟶ W` over `U` with images `g⁻¹(U)`. -/
def relProjIsoOfProj [∀ U, IsOpenImmersion (j U)]
    (hbase : ∀ U : X.AffineZariskiSite, j U ≫ g = S.projToOpen U ≫ U.1.ι)
    (hrange : ∀ U : X.AffineZariskiSite, g ⁻¹ᵁ U.1 = (j U).opensRange) : S.relProj ≅ W :=
  haveI := S.isIso_relProjDesc j hmap g hbase hrange
  asIso (S.relProjDesc j hmap)

end QuasiCoherentGradedAlgebra

end Hartshorne
