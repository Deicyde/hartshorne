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
(`AlgebraicGeometry.Scheme.relativeDifferentialsProductIso`). The isomorphism is natural: on the
summands its inverse is given by the first maps `p_X^* Ω_{X/S} ⟶ Ω_{P/S}` and
`p_Y^* Ω_{Y/S} ⟶ Ω_{P/S}` of the two transitivity sequences
(`biprod_inl_relativeDifferentialsProductIso_inv`, `biprod_inr_relativeDifferentialsProductIso_inv`),
so it sends `p_X^*(d a)` and `p_Y^*(d b)` to `d (p_X^♯ a)` and `d (p_Y^♯ b)`.

## Proof

The transitivity sequence `p_X^* Ω_{X/S} ⟶ Ω_{P/S} ⟶ Ω_{P/X} ⟶ 0` is right exact
(Hartshorne II.8.11). Its first map has a retraction: the composite
`p_X^* Ω_{X/S} ⟶ Ω_{P/S} ⟶ Ω_{P/Y}` is the base-change map of Hartshorne II.8.10, an
isomorphism, so `Ω_{P/S} ⟶ Ω_{P/Y} ≅ p_X^* Ω_{X/S}` is a retraction. The sequence therefore
splits, `Ω_{P/S} ≅ p_X^* Ω_{X/S} ⊕ Ω_{P/X}`, and `Ω_{P/X} ≅ p_Y^* Ω_{Y/S}` is base change on the
other side (`relativeDifferentialsFstIso`, through the symmetry `X ×_S Y ≅ Y ×_S X`).

For the second summand, `relativeDifferentialsFstIso_inv` identifies the inverse of
`Ω_{P/X} ≅ p_Y^* Ω_{Y/S}` with `p_Y^* Ω_{Y/S} ⟶ Ω_{P/S} ⟶ Ω_{P/X}`. Both maps are out of
`p_Y^* Ω_{Y/S}`, so by the pullback adjunction and the universal property of `Ω_{Y/S}` it is
enough to compare them on the sections `p_Y^*(d b)` (`pullbackRelativeDifferentials_hom_ext`),
where both give `d (p_Y^♯ b)`. The splitting section then restricts to that map on `p_Y^* Ω_{Y/S}`,
because the composite `p_Y^* Ω_{Y/S} ⟶ Ω_{P/S} ⟶ Ω_{P/Y}` vanishes.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- Along an isomorphism `e`, `e^* Ω_{P'/X} ≅ Ω_{P/X}`. -/
noncomputable def pullbackRelativeDifferentialsIsoOfIsIso {P P' X : Scheme.{u}} (e : P ⟶ P')
    [IsIso e] (k : P' ⟶ X) :
    (Modules.pullback e).obj (relativeDifferentials k) ≅ relativeDifferentials (e ≫ k) :=
  ((Modules.restrictFunctorIsoPullback e).app _).symm ≪≫
    (RelDiffLocal.restrictIso k e (e ≫ k) (𝟙 X) (Category.comp_id _).symm).symm

/-- The identification of differential sheaves of equal morphisms, backwards, respects the
derivations. -/
theorem relativeDifferentialsCongr_inv_d {P Z : Scheme.{u}} {k k' : P ⟶ Z} (h : k = k')
    (U : P.Opensᵒᵖ) (x : P.presheaf.obj U) :
    (relativeDifferentialsCongr h).inv.val.app U ((relativeDifferentialsDerivation k').d x) =
      (relativeDifferentialsDerivation k).d x := by
  subst h
  rw [relativeDifferentialsCongr_def]
  rfl

/-- The identification of the differential sheaf of `k` with itself is the identity. -/
theorem relativeDifferentialsCongr_rfl {P Z : Scheme.{u}} (k : P ⟶ Z) :
    relativeDifferentialsCongr (rfl : k = k) = Iso.refl _ := by
  rw [relativeDifferentialsCongr_def]
  rfl

/-- Two maps out of `q^* Ω_{Y/S}` are equal if they agree on the pulled-back differentials
`q^*(d b)`. -/
theorem pullbackRelativeDifferentials_hom_ext {P Y S : Scheme.{u}} (g : Y ⟶ S) (q : P ⟶ Y)
    {M : P.Modules} {φ ψ : (Modules.pullback q).obj (relativeDifferentials g) ⟶ M}
    (h : ∀ (V : Y.Opens) (b : Y.presheaf.obj (op V)),
      φ.val.app (op (q ⁻¹ᵁ V))
        (((Modules.pullbackPushforwardAdjunction q).unit.app (relativeDifferentials g)).val.app
          (op V) ((relativeDifferentialsDerivation g).d b)) =
      ψ.val.app (op (q ⁻¹ᵁ V))
        (((Modules.pullbackPushforwardAdjunction q).unit.app (relativeDifferentials g)).val.app
          (op V) ((relativeDifferentialsDerivation g).d b))) :
    φ = ψ := by
  apply ((Modules.pullbackPushforwardAdjunction q).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply (relativeDifferentialsHomEquiv g _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext V b
  exact h V.unop b

/-- The isomorphism `e^* Ω_{P'/X} ≅ Ω_{P/X}` sends `e^*(d c)` to `d (e^♯ c)`. -/
theorem pullbackRelativeDifferentialsIsoOfIsIso_hom_unit_d {P P' X : Scheme.{u}} (e : P ⟶ P')
    [IsIso e] (k : P' ⟶ X) (V : P'.Opens) (c : P'.presheaf.obj (op V)) :
    (pullbackRelativeDifferentialsIsoOfIsIso e k).hom.val.app (op (e ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction e).unit.app (relativeDifferentials k)).val.app
        (op V) ((relativeDifferentialsDerivation k).d c)) =
      (relativeDifferentialsDerivation (e ≫ k)).d (e.c.app (op V) c) := by
  have hW : e ''ᵁ (e ⁻¹ᵁ V) ≤ V := e.image_preimage_le V
  let r := RelDiffLocal.restrictIso k e (e ≫ k) (𝟙 X) (Category.comp_id _).symm
  have h1 : ((Modules.restrictFunctorIsoPullback e).inv.app (relativeDifferentials k)).val.app
      (op (e ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction e).unit.app (relativeDifferentials k)).val.app
        (op V) ((relativeDifferentialsDerivation k).d c)) =
      (relativeDifferentialsDerivation k).d (X := op (e ''ᵁ (e ⁻¹ᵁ V)))
        (P'.presheaf.map (homOfLE hW).op c) :=
    (Modules.restrictFunctorIsoPullback_inv_unit e _ V _).trans
      ((relativeDifferentialsDerivation k).d_map (homOfLE hW).op c).symm
  have h2 : r.inv.val.app (op (e ⁻¹ᵁ V))
      ((relativeDifferentialsDerivation k).d (X := op (e ''ᵁ (e ⁻¹ᵁ V)))
        (P'.presheaf.map (homOfLE hW).op c)) =
      (relativeDifferentialsDerivation (e ≫ k)).d
        ((e.appIso (e ⁻¹ᵁ V)).hom (P'.presheaf.map (homOfLE hW).op c)) := by
    rw [← RelDiffLocal.restrictIso_hom_d k e (e ≫ k) (𝟙 X) (Category.comp_id _).symm]
    have key : ∀ x, r.inv.val.app (op (e ⁻¹ᵁ V)) (r.hom.val.app (op (e ⁻¹ᵁ V)) x) = x :=
      fun x => congrArg (fun φ => φ.val.app (op (e ⁻¹ᵁ V)) x) r.hom_inv_id
    exact key _
  have h3 : (e.appIso (e ⁻¹ᵁ V)).hom (P'.presheaf.map (homOfLE hW).op c) = e.c.app (op V) c := by
    rw [Hom.appIso_hom', ← ConcreteCategory.comp_apply, Hom.map_appLE, Hom.appLE_eq_app]
  change r.inv.val.app (op (e ⁻¹ᵁ V))
    (((Modules.restrictFunctorIsoPullback e).inv.app (relativeDifferentials k)).val.app
      (op (e ⁻¹ᵁ V)) _) = _
  rw [h1, h2, h3]

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

namespace RelDiffProduct

/-- For an isomorphism `e : P ⟶ Y ×_S X`, `Ω_{P/X} ≅ (p_Y ∘ e)^* Ω_{Y/S}`: base change of
`Ω_{Y/S}` along `X ⟶ S`, transported along `e`. -/
noncomputable def fstIsoAux {P : Scheme.{u}} (e : P ⟶ pullback g f) [IsIso e] :
    relativeDifferentials (e ≫ pullback.snd g f) ≅
      (Modules.pullback (e ≫ pullback.fst g f)).obj (relativeDifferentials g) :=
  (pullbackRelativeDifferentialsIsoOfIsIso e (pullback.snd g f)).symm ≪≫
    (Modules.pullback e).mapIso (relativeDifferentialsBaseChangeIso g f) ≪≫
    (Modules.pullbackComp e (pullback.fst g f)).app _

theorem fstIsoAux_inv {P : Scheme.{u}} (e : P ⟶ pullback g f) [IsIso e] {p : P ⟶ X}
    {q : P ⟶ Y} (hp : e ≫ pullback.snd g f = p) (hq : e ≫ pullback.fst g f = q)
    (w : p ≫ f = q ≫ g) :
    pullbackRelativeDifferentialsToComp q g ≫ (relativeDifferentialsCongr w).inv ≫
        relativeDifferentialsCompToLeft p f =
      (Modules.pullbackCongr hq).inv.app _ ≫ (fstIsoAux f g e).inv ≫
        (relativeDifferentialsCongr hp).hom := by
  subst hp hq
  simp only [Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    relativeDifferentialsCongr_rfl, Iso.refl_hom, Category.id_comp, Category.comp_id]
  apply pullbackRelativeDifferentials_hom_ext g (e ≫ pullback.fst g f)
  intro V b
  have L : (pullbackRelativeDifferentialsToComp (e ≫ pullback.fst g f) g ≫
      (relativeDifferentialsCongr w).inv ≫
        relativeDifferentialsCompToLeft (e ≫ pullback.snd g f) f).val.app
        (op ((e ≫ pullback.fst g f) ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction (e ≫ pullback.fst g f)).unit.app
        (relativeDifferentials g)).val.app (op V) ((relativeDifferentialsDerivation g).d b)) =
      (relativeDifferentialsDerivation (e ≫ pullback.snd g f)).d
        (e.c.app (op (pullback.fst g f ⁻¹ᵁ V)) ((pullback.fst g f).c.app (op V) b)) := by
    change (relativeDifferentialsCompToLeft (e ≫ pullback.snd g f) f).val.app
      (op ((e ≫ pullback.fst g f) ⁻¹ᵁ V)) ((relativeDifferentialsCongr w).inv.val.app
        (op ((e ≫ pullback.fst g f) ⁻¹ᵁ V))
        ((pullbackRelativeDifferentialsToComp (e ≫ pullback.fst g f) g).val.app
          (op ((e ≫ pullback.fst g f) ⁻¹ᵁ V))
          (((Modules.pullbackPushforwardAdjunction (e ≫ pullback.fst g f)).unit.app
            (relativeDifferentials g)).val.app (op V) ((relativeDifferentialsDerivation g).d b)))) = _
    rw [pullbackRelativeDifferentialsToComp_unit_d, relativeDifferentialsCongr_inv_d,
      relativeDifferentialsCompToLeft_d]
    rfl
  have s1 : ((Modules.pullbackComp e (pullback.fst g f)).inv.app
      (relativeDifferentials g)).val.app (op ((e ≫ pullback.fst g f) ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction (e ≫ pullback.fst g f)).unit.app
        (relativeDifferentials g)).val.app (op V) ((relativeDifferentialsDerivation g).d b)) =
      ((Modules.pullbackPushforwardAdjunction e).unit.app
        ((Modules.pullback (pullback.fst g f)).obj (relativeDifferentials g))).val.app
        (op (pullback.fst g f ⁻¹ᵁ V))
        (((Modules.pullbackPushforwardAdjunction (pullback.fst g f)).unit.app
          (relativeDifferentials g)).val.app (op V) ((relativeDifferentialsDerivation g).d b)) :=
    Modules.pullbackComp_inv_unit e (pullback.fst g f) (relativeDifferentials g) V _
  have s2 : ((Modules.pullback e).map (baseChangeRelativeDifferentialsMap g f)).val.app
      (op (e ⁻¹ᵁ (pullback.fst g f ⁻¹ᵁ V)))
      (((Modules.pullbackPushforwardAdjunction e).unit.app
        ((Modules.pullback (pullback.fst g f)).obj (relativeDifferentials g))).val.app
        (op (pullback.fst g f ⁻¹ᵁ V))
        (((Modules.pullbackPushforwardAdjunction (pullback.fst g f)).unit.app
          (relativeDifferentials g)).val.app (op V) ((relativeDifferentialsDerivation g).d b))) =
      ((Modules.pullbackPushforwardAdjunction e).unit.app
        (relativeDifferentials (pullback.snd g f))).val.app (op (pullback.fst g f ⁻¹ᵁ V))
        ((baseChangeRelativeDifferentialsMap g f).val.app (op (pullback.fst g f ⁻¹ᵁ V))
          (((Modules.pullbackPushforwardAdjunction (pullback.fst g f)).unit.app
            (relativeDifferentials g)).val.app (op V) ((relativeDifferentialsDerivation g).d b))) :=
    Modules.pullback_map_unit e (baseChangeRelativeDifferentialsMap g f) _ _
  have R : (fstIsoAux f g e).inv.val.app (op ((e ≫ pullback.fst g f) ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction (e ≫ pullback.fst g f)).unit.app
        (relativeDifferentials g)).val.app (op V) ((relativeDifferentialsDerivation g).d b)) =
      (relativeDifferentialsDerivation (e ≫ pullback.snd g f)).d
        (e.c.app (op (pullback.fst g f ⁻¹ᵁ V)) ((pullback.fst g f).c.app (op V) b)) := by
    change (pullbackRelativeDifferentialsIsoOfIsIso e (pullback.snd g f)).hom.val.app
      (op (e ⁻¹ᵁ (pullback.fst g f ⁻¹ᵁ V)))
      (((Modules.pullback e).map (baseChangeRelativeDifferentialsMap g f)).val.app
        (op (e ⁻¹ᵁ (pullback.fst g f ⁻¹ᵁ V)))
        (((Modules.pullbackComp e (pullback.fst g f)).inv.app (relativeDifferentials g)).val.app
          (op ((e ≫ pullback.fst g f) ⁻¹ᵁ V))
          (((Modules.pullbackPushforwardAdjunction (e ≫ pullback.fst g f)).unit.app
            (relativeDifferentials g)).val.app (op V)
              ((relativeDifferentialsDerivation g).d b)))) = _
    rw [s1]
    erw [s2]
    rw [baseChangeRelativeDifferentialsMap_unit_d,
      pullbackRelativeDifferentialsIsoOfIsIso_hom_unit_d]
  exact L.trans R.symm

end RelDiffProduct

open RelDiffProduct in
/-- For `P = X ×_S Y`, `Ω_{P/X} ≅ p_Y^* Ω_{Y/S}`: base change of `Ω_{Y/S}` along `X ⟶ S`. -/
noncomputable def relativeDifferentialsFstIso :
    relativeDifferentials (pullback.fst f g) ≅
      (Modules.pullback (pullback.snd f g)).obj (relativeDifferentials g) :=
  (relativeDifferentialsCongr (pullbackSymmetry_hom_comp_snd f g)).symm ≪≫
    fstIsoAux f g (pullbackSymmetry f g).hom ≪≫
    (Modules.pullbackCongr (pullbackSymmetry_hom_comp_fst f g)).app _

open RelDiffProduct in
/-- **Naturality of `relativeDifferentialsFstIso`.** Its inverse
`p_Y^* Ω_{Y/S} ⟶ Ω_{P/X}` is the transitivity map `p_Y^* Ω_{Y/S} ⟶ Ω_{P/S}` followed by
`Ω_{P/S} ⟶ Ω_{P/X}`: it sends `p_Y^*(d b)` to `d (p_Y^♯ b)`. -/
theorem relativeDifferentialsFstIso_inv :
    pullbackRelativeDifferentialsToComp (pullback.snd f g) g ≫
        (relativeDifferentialsCongr pullback.condition).inv ≫
          relativeDifferentialsCompToLeft (pullback.fst f g) f =
      (relativeDifferentialsFstIso f g).inv := by
  rw [fstIsoAux_inv f g (pullbackSymmetry f g).hom (pullbackSymmetry_hom_comp_snd f g)
    (pullbackSymmetry_hom_comp_fst f g) pullback.condition]
  simp only [relativeDifferentialsFstIso, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    Category.assoc]

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

/-- On the second summand, the inverse of the product isomorphism is the transitivity map
`p_Y^* Ω_{Y/S} ⟶ Ω_{(X ×_S Y)/S}`, through `p_Y ∘ g = p_X ∘ f`. -/
theorem biprod_inr_relativeDifferentialsProductIso_inv :
    biprod.inr ≫ (relativeDifferentialsProductIso f g).inv =
      pullbackRelativeDifferentialsToComp (pullback.snd f g) g ≫
        (relativeDifferentialsCongr pullback.condition).inv := by
  simp only [relativeDifferentialsProductIso, ShortComplex.Splitting.isoBinaryBiproduct,
    productShortComplex, biprod.mapIso, Iso.trans_inv, Iso.refl_inv]
  erw [biprod.inr_map_assoc, biprod.inr_desc]
  change (relativeDifferentialsFstIso f g).inv ≫ productSection f g = _
  have hz := pullbackRelativeDifferentialsToComp_comp_relativeDifferentialsCompToLeft
    (pullback.snd f g) g
  rw [← relativeDifferentialsFstIso_inv, Category.assoc, Category.assoc,
    relativeDifferentialsCompToLeft_productSection, productComplement]
  simp only [Preadditive.comp_sub, Category.comp_id, productRetraction, Category.assoc,
    Iso.inv_hom_id_assoc, reassoc_of% hz, zero_comp, sub_zero]

end AlgebraicGeometry.Scheme
