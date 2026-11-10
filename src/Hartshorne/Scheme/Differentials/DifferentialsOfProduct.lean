/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.RelativeDifferentialsBaseChange

/-!
# Differentials of a product

Hartshorne, *Algebraic Geometry*, II, Exercise 8.3(a) (p. 187).

For schemes `X` and `Y` over `S`, with projections `p_X`, `p_Y` from `P = X ×_S Y`,
`Ω_{P/S} ≅ p_X^* Ω_{X/S} ⊕ p_Y^* Ω_{Y/S}`
(`AlgebraicGeometry.Scheme.relativeDifferentialsProductIso`). On the first summand the inverse is
the first map `p_X^* Ω_{X/S} ⟶ Ω_{P/S}` of the transitivity sequence
(`biprod_inl_relativeDifferentialsProductIso_inv`).

## Proof

The transitivity sequence `p_X^* Ω_{X/S} ⟶ Ω_{P/S} ⟶ Ω_{P/X} ⟶ 0` is right exact
(Hartshorne II.8.11). Its first map has a retraction: the composite
`p_X^* Ω_{X/S} ⟶ Ω_{P/S} ⟶ Ω_{P/Y}` is the base-change map of Hartshorne II.8.10, an
isomorphism, so `Ω_{P/S} ⟶ Ω_{P/Y} ≅ p_X^* Ω_{X/S}` is a retraction. The sequence therefore
splits, `Ω_{P/S} ≅ p_X^* Ω_{X/S} ⊕ Ω_{P/X}`, and `Ω_{P/X} ≅ p_Y^* Ω_{Y/S}` is base change on the
other side (`relativeDifferentialsFstIso`, through the symmetry `X ×_S Y ≅ Y ×_S X`).
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- Along an isomorphism `e`, `e^* Ω_{P'/X} ≅ Ω_{P/X}`. -/
noncomputable def pullbackRelativeDifferentialsIsoOfIsIso {P P' X : Scheme.{u}} (e : P ⟶ P')
    [IsIso e] (k : P' ⟶ X) :
    (Modules.pullback e).obj (relativeDifferentials k) ≅ relativeDifferentials (e ≫ k) :=
  ((Modules.restrictFunctorIsoPullback e).app _).symm ≪≫
    (RelDiffLocal.restrictIso k e (e ≫ k) (𝟙 X) (Category.comp_id _).symm).symm

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- For `P = X ×_S Y`, `Ω_{P/X} ≅ p_Y^* Ω_{Y/S}`: base change of `Ω_{Y/S}` along `X ⟶ S`. -/
noncomputable def relativeDifferentialsFstIso :
    relativeDifferentials (pullback.fst f g) ≅
      (Modules.pullback (pullback.snd f g)).obj (relativeDifferentials g) :=
  (relativeDifferentialsCongr (pullbackSymmetry_hom_comp_snd f g)).symm ≪≫
    (pullbackRelativeDifferentialsIsoOfIsIso (pullbackSymmetry f g).hom (pullback.snd g f)).symm ≪≫
    (Modules.pullback (pullbackSymmetry f g).hom).mapIso (relativeDifferentialsBaseChangeIso g f) ≪≫
    (Modules.pullbackComp (pullbackSymmetry f g).hom (pullback.fst g f)).app _ ≪≫
    (Modules.pullbackCongr (pullbackSymmetry_hom_comp_fst f g)).app _

namespace RelDiffProduct

/-- The retraction `Ω_{P/S} ⟶ p_X^* Ω_{X/S}` of the first transitivity map, through
`Ω_{P/S} ⟶ Ω_{P/Y} ≅ p_X^* Ω_{X/S}`. -/
noncomputable def productRetraction :
    relativeDifferentials (pullback.fst f g ≫ f) ⟶
      (Modules.pullback (pullback.fst f g)).obj (relativeDifferentials f) :=
  (relativeDifferentialsCongr pullback.condition).hom ≫
    relativeDifferentialsCompToLeft (pullback.snd f g) g ≫
      (relativeDifferentialsBaseChangeIso f g).hom

theorem pullbackRelativeDifferentialsToComp_productRetraction :
    pullbackRelativeDifferentialsToComp (pullback.fst f g) f ≫ productRetraction f g = 𝟙 _ := by
  have := isIso_baseChangeRelativeDifferentialsMap f g
  unfold productRetraction relativeDifferentialsBaseChangeIso
  rw [Iso.symm_hom, asIso_inv]
  change baseChangeRelativeDifferentialsMap f g ≫ inv (baseChangeRelativeDifferentialsMap f g) = _
  exact IsIso.hom_inv_id _

/-- The transitivity sequence `p_X^* Ω_{X/S} ⟶ Ω_{P/S} ⟶ Ω_{P/X}` as a short complex. -/
noncomputable def productShortComplex : ShortComplex (pullback f g).Modules :=
  ShortComplex.mk (pullbackRelativeDifferentialsToComp (pullback.fst f g) f)
    (relativeDifferentialsCompToLeft (pullback.fst f g) f)
    (pullbackRelativeDifferentialsToComp_comp_relativeDifferentialsCompToLeft _ _)

/-- The endomorphism `1 - α ∘ r` of `Ω_{P/S}`, which kills the image of `α`. -/
noncomputable def productComplement :
    relativeDifferentials (pullback.fst f g ≫ f) ⟶ relativeDifferentials (pullback.fst f g ≫ f) :=
  𝟙 _ - productRetraction f g ≫ pullbackRelativeDifferentialsToComp (pullback.fst f g) f

theorem pullbackRelativeDifferentialsToComp_productComplement :
    pullbackRelativeDifferentialsToComp (pullback.fst f g) f ≫ productComplement f g = 0 := by
  unfold productComplement
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    pullbackRelativeDifferentialsToComp_productRetraction, Category.id_comp, sub_self]

/-- The section `Ω_{P/X} ⟶ Ω_{P/S}` of the second transitivity map, induced by
`1 - α ∘ r` on the cokernel. -/
noncomputable def productSection :
    relativeDifferentials (pullback.fst f g) ⟶ relativeDifferentials (pullback.fst f g ≫ f) :=
  (relativeDifferentialsTransitivityIsColimit (pullback.fst f g) f).desc
    (CokernelCofork.ofπ (productComplement f g)
      (pullbackRelativeDifferentialsToComp_productComplement f g))

theorem relativeDifferentialsCompToLeft_productSection :
    relativeDifferentialsCompToLeft (pullback.fst f g) f ≫ productSection f g =
      productComplement f g :=
  (relativeDifferentialsTransitivityIsColimit (pullback.fst f g) f).fac _ WalkingParallelPair.one

/-- The transitivity sequence for `X ×_S Y ⟶ X ⟶ S` splits. -/
noncomputable def productSplitting : (productShortComplex f g).Splitting where
  r := productRetraction f g
  s := productSection f g
  f_r := pullbackRelativeDifferentialsToComp_productRetraction f g
  s_g := by
    apply Cofork.IsColimit.hom_ext (relativeDifferentialsTransitivityIsColimit (pullback.fst f g) f)
    change relativeDifferentialsCompToLeft (pullback.fst f g) f ≫ productSection f g ≫
      relativeDifferentialsCompToLeft (pullback.fst f g) f =
        relativeDifferentialsCompToLeft (pullback.fst f g) f ≫ 𝟙 _
    rw [← Category.assoc, relativeDifferentialsCompToLeft_productSection, productComplement]
    simp only [Preadditive.sub_comp, Category.assoc,
      pullbackRelativeDifferentialsToComp_comp_relativeDifferentialsCompToLeft,
      comp_zero, sub_zero, Category.id_comp, Category.comp_id]
  id := by
    change productRetraction f g ≫ pullbackRelativeDifferentialsToComp (pullback.fst f g) f +
      relativeDifferentialsCompToLeft (pullback.fst f g) f ≫ productSection f g = 𝟙 _
    rw [relativeDifferentialsCompToLeft_productSection, productComplement, add_sub_cancel]

end RelDiffProduct

open RelDiffProduct

/-- **Hartshorne II, Exercise 8.3(a).** For schemes `X` and `Y` over `S`, with projections
`p_X`, `p_Y` from `X ×_S Y`, there is a natural isomorphism
`Ω_{(X ×_S Y)/S} ≅ p_X^* Ω_{X/S} ⊕ p_Y^* Ω_{Y/S}`. -/
noncomputable def relativeDifferentialsProductIso :
    relativeDifferentials (pullback.fst f g ≫ f) ≅
      (Modules.pullback (pullback.fst f g)).obj (relativeDifferentials f) ⊞
        (Modules.pullback (pullback.snd f g)).obj (relativeDifferentials g) :=
  (productSplitting f g).isoBinaryBiproduct ≪≫
    biprod.mapIso (Iso.refl _) (relativeDifferentialsFstIso f g)

/-- On the first summand, the inverse of the product isomorphism is the transitivity map
`p_X^* Ω_{X/S} ⟶ Ω_{(X ×_S Y)/S}`. -/
theorem biprod_inl_relativeDifferentialsProductIso_inv :
    biprod.inl ≫ (relativeDifferentialsProductIso f g).inv =
      pullbackRelativeDifferentialsToComp (pullback.fst f g) f := by
  simp only [relativeDifferentialsProductIso, ShortComplex.Splitting.isoBinaryBiproduct,
    productShortComplex, biprod.mapIso, Iso.trans_inv, Iso.refl_inv]
  erw [biprod.inl_map_assoc, Category.id_comp, biprod.inl_desc]

end AlgebraicGeometry.Scheme
