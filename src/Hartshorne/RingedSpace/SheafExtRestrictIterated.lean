/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtRestrict

/-!
# Right derived functors and exact functors: computation with any injective resolution

Let `Φ : C ⥤ D` be an exact functor between abelian categories preserving injective objects, and
`e : H ⋙ Φ ≅ Φ ⋙ H'`. The isomorphism `Φ(RⁿH(G)) ≅ RⁿH'(Φ(G))` of
`Hartshorne.RightDerivedComp.rightDerivedCompIso` is built from the chosen injective resolution of
`G`. Here it is computed from an arbitrary injective resolution `I` of `G`
(`Hartshorne.RightDerivedComp.rightDerivedCompIso_eq_ofResolution`): it is
`Φ(RⁿH(G)) ≅ Φ(hⁿ(H(I))) ≅ hⁿ(H'(Φ(I))) ≅ RⁿH'(Φ(G))`, where `Φ(I)` is the image injective
resolution of `Φ(G)`. In particular this applies to `Hartshorne.Ringed.sheafExtRestrictIso`
(`Hartshorne.Ringed.sheafExtRestrictIso_eq_ofResolution`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace RightDerivedComp

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {Φ : C ⥤ D} [Φ.Additive] [Φ.PreservesHomology]
  (hΦ : ∀ I : C, Injective I → Injective (Φ.obj I))
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  {H : C ⥤ C} [H.Additive] {H' : D ⥤ D} [H'.Additive] (e : H ⋙ Φ ≅ Φ ⋙ H')

/-- The isomorphism `Φ(RⁿH(G)) ≅ RⁿH'(Φ(G))` computed from an injective resolution `I` of `G`:
`Φ(RⁿH(G)) ≅ Φ(hⁿ(H(I))) ≅ hⁿ(H'(Φ(I))) ≅ RⁿH'(Φ(G))`. -/
noncomputable def rightDerivedCompIsoOfResolution {G : C} (I : InjectiveResolution G) (n : ℕ) :
    Φ.obj ((H.rightDerived n).obj G) ≅ (H'.rightDerived n).obj (Φ.obj G) :=
  Φ.mapIso (I.isoRightDerivedObj H n) ≪≫ (homologyCompIso e n).app I.cocomplex ≪≫
    ((mapInjectiveResolution hΦ I).isoRightDerivedObj H' n).symm

/-- Naturality of `rightDerivedCompIsoOfResolution`, for a chain map of injective resolutions over
a morphism `g : G ⟶ G'`. -/
lemma rightDerivedCompIsoOfResolution_hom_naturality {G G' : C} (g : G ⟶ G')
    (I : InjectiveResolution G) (I' : InjectiveResolution G') (φ : I.cocomplex ⟶ I'.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = g ≫ I'.ι.f 0) (n : ℕ) :
    Φ.map ((H.rightDerived n).map g) ≫ (rightDerivedCompIsoOfResolution hΦ e I' n).hom =
      (rightDerivedCompIsoOfResolution hΦ e I n).hom ≫ (H'.rightDerived n).map (Φ.map g) := by
  have h1 := InjectiveResolution.isoRightDerivedObj_hom_naturality g I I' φ comm H n
  have h2 := (homologyCompIso e n).hom.naturality φ
  have hcc : (mapInjectiveResolution hΦ I).ι ≫ (Φ.mapHomologicalComplex _).map φ =
      (CochainComplex.single₀ D).map (Φ.map g) ≫ (mapInjectiveResolution hΦ I').ι := by
    have hφ : I.ι ≫ φ = (CochainComplex.single₀ C).map g ≫ I'.ι := by
      ext
      simpa using comm
    simp only [mapInjectiveResolution, Category.assoc, ← Functor.map_comp, hφ]
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _)
      ((HomologicalComplex.singleMapHomologicalComplex Φ _ 0).inv.naturality g).symm
  have hc : (mapInjectiveResolution hΦ I).ι.f 0 ≫ ((Φ.mapHomologicalComplex _).map φ).f 0 =
      Φ.map g ≫ (mapInjectiveResolution hΦ I').ι.f 0 := by
    rw [← HomologicalComplex.comp_f, hcc, HomologicalComplex.comp_f,
      CochainComplex.single₀_map_f_zero]
    rfl
  have h4 := InjectiveResolution.isoRightDerivedObj_hom_naturality (Φ.map g)
    (mapInjectiveResolution hΦ I) (mapInjectiveResolution hΦ I')
    ((Φ.mapHomologicalComplex _).map φ) hc H' n
  have h4' := (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 h4).trans (Category.assoc _ _ _))
  simp only [rightDerivedCompIsoOfResolution, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc]
  refine congrArg (_ ≫ ·) ?_
  rw [← Category.assoc]
  erw [h2]
  rw [Category.assoc]
  exact congrArg (_ ≫ ·) h4'.symm

/-- `rightDerivedCompIsoOfResolution` does not depend on the injective resolution. -/
lemma rightDerivedCompIsoOfResolution_eq {G : C} (I I' : InjectiveResolution G) (n : ℕ) :
    rightDerivedCompIsoOfResolution hΦ e I n = rightDerivedCompIsoOfResolution hΦ e I' n := by
  ext
  have h := rightDerivedCompIsoOfResolution_hom_naturality hΦ e (𝟙 G) I I'
    (InjectiveResolution.desc (𝟙 G) I' I) (InjectiveResolution.desc_commutes_zero _ _ _) n
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- **`rightDerivedCompIso` from any injective resolution.** -/
lemma rightDerivedCompIso_eq_ofResolution {G : C} (I : InjectiveResolution G) (n : ℕ) :
    rightDerivedCompIso hΦ e G n = rightDerivedCompIsoOfResolution hΦ e I n :=
  rightDerivedCompIsoOfResolution_eq hΦ e (injectiveResolution G) I n

section Homology

open ShortComplex in
/-- `mapHomologyIso` for a composite functor. -/
lemma mapHomologyIso_comp {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C]
    [Abelian D] [Abelian E] (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] :
    S.mapHomologyIso (F ⋙ G) = (S.map F).mapHomologyIso G ≪≫ G.mapIso (S.mapHomologyIso F) := by
  rw [LeftHomologyData.mapHomologyIso_eq S.homologyData.left (F ⋙ G),
    LeftHomologyData.mapHomologyIso_eq S.homologyData.left F,
    LeftHomologyData.mapHomologyIso_eq (S.homologyData.left.map F) G]
  ext
  dsimp only [Iso.trans, Functor.mapIso, Iso.symm]
  have h : G.map (S.homologyData.left.map F).homologyIso.inv ≫
      G.map ((S.homologyData.left.map F).homologyIso.hom ≫ F.map S.homologyData.left.homologyIso.inv) =
      G.map (F.map S.homologyData.left.homologyIso.inv) := by
    rw [← Functor.map_comp]
    exact congrArg G.map (Iso.inv_hom_id_assoc _ _)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  erw [h]
  have hc : (S.homologyData.left.map (F ⋙ G)).cyclesIso.hom =
      ((S.homologyData.left.map F).map G).cyclesIso.hom := by
    refine (cancel_mono (S.homologyData.left.map (F ⋙ G)).i).1 ?_
    exact (S.homologyData.left.map (F ⋙ G)).cyclesIso_hom_comp_i.trans
      ((S.homologyData.left.map F).map G).cyclesIso_hom_comp_i.symm
  have hh : (S.homologyData.left.map (F ⋙ G)).homologyIso.hom =
      ((S.homologyData.left.map F).map G).homologyIso.hom := by
    refine (cancel_epi (S.map (F ⋙ G)).homologyπ).1 ?_
    exact ((S.homologyData.left.map (F ⋙ G)).homologyπ_comp_homologyIso_hom).trans
      ((congrArg (· ≫ _) hc).trans
        ((S.homologyData.left.map F).map G).homologyπ_comp_homologyIso_hom.symm)
  erw [hh]
  rfl

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {Φ : C ⥤ D} [Φ.Additive] [Φ.PreservesHomology]
  {H : C ⥤ C} [H.Additive] {H' : D ⥤ D} [H'.Additive] (e : H ⋙ Φ ≅ Φ ⋙ H')

/-- The components of `homologyCompIso`: `Φ(hⁿ(H(K))) ≅ hⁿ(Φ(H(K))) ⟶ hⁿ(H'(Φ(K)))`. -/
lemma homologyCompIso_hom_app (n : ℕ) (K : CochainComplex C ℕ) :
    (homologyCompIso e n).hom.app K =
      ((((H.mapHomologicalComplex _).obj K).sc n).mapHomologyIso Φ).inv ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex e.hom _).app K) n := by
  simp only [homologyCompIso, homologyFunctorCompNatIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  refine congrArg₂ (· ≫ ·) rfl (congrArg (fun φ => HomologicalComplex.homologyMap φ n) ?_)
  ext i
  simp only [Functor.mapHomologicalComplexCompIso, HomologicalComplex.comp_f]
  exact (Category.id_comp _).trans (Category.comp_id _)

end Homology

section Composite

open ShortComplex

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- A diagram chase used to compare two composites of homology isomorphisms. -/
lemma diagram_aux {E : Type*} [Category E] {P0 P1 P2 P3 P4 P5 Q1 R0 R1 R2 R3 R4 T1 : E}
    {a : P0 ⟶ P1} {b : P1 ⟶ P2} {d : P2 ⟶ P3} {x : P3 ⟶ P4} {y : P4 ⟶ P5} {d' : P1 ⟶ Q1}
    {b' : Q1 ⟶ P3} {M : P0 ⟶ Q1} {γ : P0 ⟶ R0} {a' : R0 ⟶ R1} {β : R1 ⟶ R2} {δ : R2 ⟶ R3}
    {u : R3 ⟶ R4} {v : R4 ⟶ P5} {δ' : R1 ⟶ T1} {β' : T1 ⟶ R3} {N : R0 ⟶ T1} {κ : Q1 ⟶ T1}
    (h1 : b ≫ d = d' ≫ b') (h2 : a ≫ d' = M) (h1' : β ≫ δ = δ' ≫ β') (h2' : a' ≫ δ' = N)
    (h3 : γ ≫ N = M ≫ κ) (h4 : b' ≫ x ≫ y = κ ≫ β' ≫ u ≫ v) :
    a ≫ b ≫ d ≫ x ≫ y = γ ≫ a' ≫ β ≫ δ ≫ u ≫ v := by
  rw [reassoc_of% h1, reassoc_of% h2, h4, reassoc_of% h1', reassoc_of% h2', reassoc_of% h3]

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- `diagram_aux` with the last maps induced by morphisms of short complexes. -/
lemma diagram_aux' {E : Type*} [Category E] [Abelian E] {P0 P1 P2 R0 R1 R2 : E}
    {SQ1 SP3 SP4 SP5 ST1 SR3 SR4 : ShortComplex E} {a : P0 ⟶ P1} {b : P1 ⟶ P2}
    {d : P2 ⟶ SP3.homology} {X : SP3 ⟶ SP4} {Y : SP4 ⟶ SP5} {d' : P1 ⟶ SQ1.homology}
    {B' : SQ1 ⟶ SP3} {M : P0 ⟶ SQ1.homology} {γ : P0 ⟶ R0} {a' : R0 ⟶ R1} {β : R1 ⟶ R2}
    {δ : R2 ⟶ SR3.homology} {U : SR3 ⟶ SR4} {V : SR4 ⟶ SP5} {δ' : R1 ⟶ ST1.homology}
    {Bβ : ST1 ⟶ SR3} {N : R0 ⟶ ST1.homology} {K : SQ1 ⟶ ST1}
    (h1 : b ≫ d = d' ≫ ShortComplex.homologyMap B') (h2 : a ≫ d' = M)
    (h1' : β ≫ δ = δ' ≫ ShortComplex.homologyMap Bβ) (h2' : a' ≫ δ' = N)
    (h3 : γ ≫ N = M ≫ ShortComplex.homologyMap K) (h4 : B' ≫ X ≫ Y = K ≫ Bβ ≫ U ≫ V) :
    a ≫ b ≫ d ≫ ShortComplex.homologyMap X ≫ ShortComplex.homologyMap Y =
      γ ≫ a' ≫ β ≫ δ ≫ ShortComplex.homologyMap U ≫ ShortComplex.homologyMap V := by
  refine diagram_aux h1 h2 h1' h2' h3 ?_
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
    ← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
    ← ShortComplex.homologyMap_comp, h4]

variable {C D₁ D₂ E : Type*} [Category C] [Category D₁] [Category D₂] [Category E] [Abelian C]
  [Abelian D₁] [Abelian D₂] [Abelian E] {Φ₁ : C ⥤ D₁} {Φ₂ : D₁ ⥤ E} {Ψ₁ : C ⥤ D₂} {Ψ₂ : D₂ ⥤ E}
  [Φ₁.Additive] [Φ₂.Additive] [Ψ₁.Additive] [Ψ₂.Additive]
  [PreservesFiniteLimits Φ₁] [PreservesFiniteColimits Φ₁] [PreservesFiniteLimits Φ₂]
  [PreservesFiniteColimits Φ₂] [PreservesFiniteLimits Ψ₁] [PreservesFiniteColimits Ψ₁]
  [PreservesFiniteLimits Ψ₂] [PreservesFiniteColimits Ψ₂]
  {H : C ⥤ C} {H₁ : D₁ ⥤ D₁} {K₁ : D₂ ⥤ D₂} {H₂ K₂ : E ⥤ E} [H.Additive] [H₁.Additive]
  [K₁.Additive] [H₂.Additive] [K₂.Additive]
  (e₁ : H ⋙ Φ₁ ≅ Φ₁ ⋙ H₁) (e₂ : H₁ ⋙ Φ₂ ≅ Φ₂ ⋙ H₂) (f₁ : H ⋙ Ψ₁ ≅ Ψ₁ ⋙ K₁)
  (f₂ : K₁ ⋙ Ψ₂ ≅ Ψ₂ ⋙ K₂) (c : Φ₁ ⋙ Φ₂ ≅ Ψ₁ ⋙ Ψ₂) (θ : K₂ ⟶ H₂)

include e₁ e₂ f₁ f₂ c θ in
/-- Short complex form of `homologyCompIso_comp_naturality`. -/
lemma mapHomologyIso_comp_naturality
    (hθ : ∀ Y, Φ₂.map (e₁.hom.app Y) ≫ e₂.hom.app (Φ₁.obj Y) ≫ H₂.map (c.hom.app Y) =
      c.hom.app (H.obj Y) ≫ Ψ₂.map (f₁.hom.app Y) ≫ f₂.hom.app (Ψ₁.obj Y) ≫
        θ.app (Ψ₂.obj (Ψ₁.obj Y)))
    (S : ShortComplex C) :
    Φ₂.map ((S.map H).mapHomologyIso Φ₁).inv ≫ Φ₂.map (homologyMap (S.mapNatTrans e₁.hom)) ≫
        (((S.map Φ₁).map H₁).mapHomologyIso Φ₂).inv ≫
          homologyMap ((S.map Φ₁).mapNatTrans e₂.hom) ≫
            homologyMap (H₂.mapShortComplex.map (S.mapNatTrans c.hom)) =
      c.hom.app _ ≫ Ψ₂.map ((S.map H).mapHomologyIso Ψ₁).inv ≫
        Ψ₂.map (homologyMap (S.mapNatTrans f₁.hom)) ≫
          (((S.map Ψ₁).map K₁).mapHomologyIso Ψ₂).inv ≫
            homologyMap ((S.map Ψ₁).mapNatTrans f₂.hom) ≫
              homologyMap (((S.map Ψ₁).map Ψ₂).mapNatTrans θ) := by
  have h1 : Φ₂.map (homologyMap (S.mapNatTrans e₁.hom)) ≫
      (((S.map Φ₁).map H₁).mapHomologyIso Φ₂).inv =
      (((S.map H).map Φ₁).mapHomologyIso Φ₂).inv ≫
        homologyMap (Φ₂.mapShortComplex.map (S.mapNatTrans e₁.hom)) :=
    ShortComplex.mapHomologyIso_inv_naturality _ _
  have h1' : Ψ₂.map (homologyMap (S.mapNatTrans f₁.hom)) ≫
      (((S.map Ψ₁).map K₁).mapHomologyIso Ψ₂).inv =
      (((S.map H).map Ψ₁).mapHomologyIso Ψ₂).inv ≫
        homologyMap (Ψ₂.mapShortComplex.map (S.mapNatTrans f₁.hom)) :=
    ShortComplex.mapHomologyIso_inv_naturality _ _
  have h2 : Φ₂.map ((S.map H).mapHomologyIso Φ₁).inv ≫
      (((S.map H).map Φ₁).mapHomologyIso Φ₂).inv = ((S.map H).mapHomologyIso (Φ₁ ⋙ Φ₂)).inv := by
    rw [mapHomologyIso_comp]
    rfl
  have h2' : Ψ₂.map ((S.map H).mapHomologyIso Ψ₁).inv ≫
      (((S.map H).map Ψ₁).mapHomologyIso Ψ₂).inv = ((S.map H).mapHomologyIso (Ψ₁ ⋙ Ψ₂)).inv := by
    rw [mapHomologyIso_comp]
    rfl
  have h3 : c.hom.app (S.map H).homology ≫ ((S.map H).mapHomologyIso (Ψ₁ ⋙ Ψ₂)).inv =
      ((S.map H).mapHomologyIso (Φ₁ ⋙ Φ₂)).inv ≫ homologyMap ((S.map H).mapNatTrans c.hom) := by
    rw [homologyMap_mapNatTrans, Iso.inv_hom_id_assoc]
  have h4' : Φ₂.mapShortComplex.map (S.mapNatTrans e₁.hom) ≫ (S.map Φ₁).mapNatTrans e₂.hom ≫
      H₂.mapShortComplex.map (S.mapNatTrans c.hom) =
      (S.map H).mapNatTrans c.hom ≫ Ψ₂.mapShortComplex.map (S.mapNatTrans f₁.hom) ≫
        (S.map Ψ₁).mapNatTrans f₂.hom ≫ ((S.map Ψ₁).map Ψ₂).mapNatTrans θ := by
    ext <;> exact hθ _
  exact diagram_aux' h1 h2 h1' h2' h3 h4'

end Composite

end RightDerivedComp

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (U : Opens X)

attribute [local instance 2000] Abelian.toPreadditive

/-- `ℰxtⁿ_X(F, G)|_U ≅ ℰxtⁿ_U(F|_U, G|_U)` is the isomorphism of right derived functors given by
restriction to `U`. -/
lemma sheafExtRestrictIso_eq_rightDerivedCompIso (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (n : ℕ) :
    sheafExtRestrictIso U F G n = RightDerivedComp.rightDerivedCompIso (Φ := moduleRestrict U)
      (H := moduleSheafHomFunctor F) (H' := moduleSheafHomFunctor ((moduleRestrict U).obj F))
      (fun I _ => injective_moduleSheafRestrict_obj U (ringCatSheafOf R) I)
      (homRestrictIso U F) G n :=
  rfl

/-- **`ℰxtⁿ_X(F, G)|_U ≅ ℰxtⁿ_U(F|_U, G|_U)` from any injective resolution** `G ⟶ I^•`: it is
`ℰxtⁿ_X(F, G)|_U ≅ hⁿ(ℋom_X(F, I^•))|_U ≅ hⁿ(ℋom_U(F|_U, I^•|_U)) ≅ ℰxtⁿ_U(F|_U, G|_U)`. -/
lemma sheafExtRestrictIso_eq_ofResolution (F : SheafOfModules.{u} (ringCatSheafOf R))
    {G : SheafOfModules.{u} (ringCatSheafOf R)} (I : InjectiveResolution G) (n : ℕ) :
    sheafExtRestrictIso U F G n = RightDerivedComp.rightDerivedCompIsoOfResolution
      (Φ := moduleRestrict U) (H := moduleSheafHomFunctor F)
      (H' := moduleSheafHomFunctor ((moduleRestrict U).obj F))
      (fun I _ => injective_moduleSheafRestrict_obj U (ringCatSheafOf R) I)
      (homRestrictIso U F) I n :=
  RightDerivedComp.rightDerivedCompIso_eq_ofResolution _ _ I n

end Ringed

end Hartshorne
