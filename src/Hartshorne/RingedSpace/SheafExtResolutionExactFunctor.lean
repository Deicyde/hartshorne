/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtRestrictCompose
import Hartshorne.RingedSpace.SheafExtResolutionNaturality

/-!
# Resolutions computing `ℰxt` and exact functors

Let `Φ` be an exact functor between abelian categories that preserves injective objects, such as
the restriction of `𝒪_X`-modules to an open subset or the transport of modules along a
homeomorphism, together with identifications `Φ(ℋom(F, G)) ≅ ℋom(ΦF, ΦG)`. The isomorphisms
`Φ(ℰxtⁿ(F, G)) ≅ ℰxtⁿ(ΦF, ΦG)` are compatible with:

* the connecting morphisms of the homology sequence of a short exact sequence of complexes
  (`Hartshorne.ExactFunctorHomology.δ_map`);
* the connecting morphisms of the contravariant long exact sequence of `ℰxt`
  (`Hartshorne.Ringed.SheafExtContravariant.δ_comp_extCompIso`) and the identification
  `ℋom = ℰxt⁰` (`Hartshorne.Ringed.SheafExtContravariant.η_comp_extCompIso`).

As in `Hartshorne.RingedSpace.SheafExtLocallyFreeResolution`, the homological algebra is done for
abstract bifunctors `H : Cᵒᵖ ⥤ C ⥤ C` and `H' : Dᵒᵖ ⥤ D ⥤ D`.
-/

universe u v' u' v'' u''

open CategoryTheory Limits Opposite

namespace Hartshorne

namespace ExactFunctorHomology

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

set_option backward.isDefEq.respectTransparency false in
open ShortComplex in
@[reassoc]
lemma homologyπ_mapHomologyIso_hom (S : ShortComplex C) :
    (S.map Φ).homologyπ ≫ (S.mapHomologyIso Φ).hom =
      (S.mapCyclesIso Φ).hom ≫ Φ.map S.homologyπ := by
  rw [S.leftHomologyData.mapHomologyIso_eq Φ, S.leftHomologyData.mapCyclesIso_eq Φ]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [(S.leftHomologyData.map Φ).homologyπ_comp_homologyIso_hom_assoc]
  congr 1
  have h := S.leftHomologyData.homologyπ_comp_homologyIso_hom
  rw [← Φ.map_comp]
  refine (Φ.map_comp _ _).symm.trans (congrArg Φ.map ?_)
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
open ShortComplex in
@[reassoc]
lemma mapHomologyIso_inv_homologyι (S : ShortComplex C) :
    (S.mapHomologyIso Φ).inv ≫ (S.map Φ).homologyι =
      Φ.map S.homologyι ≫ (S.mapOpcyclesIso Φ).inv := by
  rw [← S.mapHomologyIso'_eq_mapHomologyIso Φ, S.rightHomologyData.mapHomologyIso'_eq Φ,
    S.rightHomologyData.mapOpcyclesIso_eq Φ]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc]
  rw [(S.rightHomologyData.map Φ).homologyIso_inv_comp_homologyι]
  change Φ.map _ ≫ Φ.map S.rightHomologyData.ι ≫ _ = _
  rw [← Φ.map_comp_assoc, S.rightHomologyData.homologyIso_hom_comp_ι, Φ.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
open ShortComplex in
@[reassoc]
lemma pOpcycles_mapOpcyclesIso_hom (S : ShortComplex C) :
    (S.map Φ).pOpcycles ≫ (S.mapOpcyclesIso Φ).hom = Φ.map S.pOpcycles := by
  rw [S.rightHomologyData.mapOpcyclesIso_eq Φ]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [(S.rightHomologyData.map Φ).pOpcycles_comp_opcyclesIso_hom_assoc]
  change Φ.map S.rightHomologyData.p ≫ _ = _
  rw [← Φ.map_comp, S.rightHomologyData.p_comp_opcyclesIso_inv]

variable {ι : Type*} {c : ComplexShape ι}

set_option backward.isDefEq.respectTransparency false in
open ShortComplex in
@[reassoc]
lemma mapCyclesIso_inv_iCycles (S : ShortComplex C) :
    (S.mapCyclesIso Φ).inv ≫ (S.map Φ).iCycles = Φ.map S.iCycles := by
  rw [← S.mapCyclesIso_hom_iCycles Φ, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
open ShortComplex in
@[reassoc]
lemma mapOpcyclesIso_inv_fromOpcycles (K : HomologicalComplex C c) (i j : ι) :
    ((K.sc i).mapOpcyclesIso Φ).inv ≫ ((Φ.mapHomologicalComplex c).obj K).fromOpcycles i j =
      Φ.map (K.fromOpcycles i j) := by
  have : Epi (Φ.map (K.pOpcycles i)) := Φ.map_epi _
  rw [← cancel_epi (Φ.map (K.pOpcycles i)), ← Φ.map_comp, HomologicalComplex.p_fromOpcycles]
  erw [← pOpcycles_mapOpcyclesIso_hom_assoc Φ (K.sc i), Iso.hom_inv_id_assoc]
  exact ((Φ.mapHomologicalComplex c).obj K).p_fromOpcycles i j

set_option backward.isDefEq.respectTransparency false in
/-- **The connecting morphism of the homology sequence commutes with an exact functor.** -/
lemma δ_map {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i j : ι)
    (hij : c.Rel i j) :
    (hS.map_of_exact (Φ.mapHomologicalComplex c)).δ i j hij ≫
        ((S.X₁.sc j).mapHomologyIso Φ).hom =
      ((S.X₃.sc i).mapHomologyIso Φ).hom ≫ Φ.map (hS.δ i j hij) := by
  let SI := HomologicalComplex.HomologySequence.snakeInput hS i j hij
  have hδ : hS.δ i j hij = SI.δ := rfl
  have : Epi (Φ.map (pullback.snd SI.L₁.g SI.v₀₁.τ₃) ≫
    ((S.X₃.sc i).mapHomologyIso Φ).inv) := epi_comp _ _
  rw [← cancel_epi (Φ.map (pullback.snd SI.L₁.g SI.v₀₁.τ₃) ≫
    ((S.X₃.sc i).mapHomologyIso Φ).inv)]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Φ.map_comp, hδ, SI.snd_δ]
  have h₂ : (Φ.map (pullback.fst SI.L₁.g SI.v₀₁.τ₃) ≫ ((S.X₂.sc i).mapOpcyclesIso Φ).inv) ≫
      HomologicalComplex.opcyclesMap (S.map (Φ.mapHomologicalComplex c)).g i =
      (Φ.map (pullback.snd SI.L₁.g SI.v₀₁.τ₃) ≫ ((S.X₃.sc i).mapHomologyIso Φ).inv) ≫
        (S.map (Φ.mapHomologicalComplex c)).X₃.homologyι i := by
    have n := ShortComplex.mapOpcyclesIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor C c i).map S.g) Φ
    rw [Category.assoc, Category.assoc]
    refine (congrArg (Φ.map (pullback.fst SI.L₁.g SI.v₀₁.τ₃) ≫ ·) n.symm).trans ?_
    refine Eq.trans ?_ (congrArg (Φ.map (pullback.snd SI.L₁.g SI.v₀₁.τ₃) ≫ ·)
      (mapHomologyIso_inv_homologyι Φ (S.X₃.sc i)).symm)
    rw [← Φ.map_comp_assoc, ← Φ.map_comp_assoc]
    exact congrArg (fun f => Φ.map f ≫ _) pullback.condition
  have h₁ : (Φ.map SI.φ₁ ≫ ((S.X₁.sc j).mapCyclesIso Φ).inv) ≫
      HomologicalComplex.cyclesMap (S.map (Φ.mapHomologicalComplex c)).f j =
      (Φ.map (pullback.fst SI.L₁.g SI.v₀₁.τ₃) ≫ ((S.X₂.sc i).mapOpcyclesIso Φ).inv) ≫
        (S.map (Φ.mapHomologicalComplex c)).X₂.opcyclesToCycles i j := by
    rw [← cancel_mono ((S.map (Φ.mapHomologicalComplex c)).X₂.iCycles j)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.opcyclesToCycles_iCycles]
    erw [mapCyclesIso_inv_iCycles_assoc Φ (S.X₁.sc j), mapOpcyclesIso_inv_fromOpcycles Φ S.X₂ i j]
    change Φ.map _ ≫ Φ.map _ ≫ Φ.map (S.f.f j) = _
    rw [← Φ.map_comp, ← Φ.map_comp, ← Φ.map_comp]
    refine congrArg Φ.map ?_
    have e₁ := SI.φ₁_L₂_f
    have e₂ : SI.L₂.f = HomologicalComplex.cyclesMap S.f j := rfl
    rw [e₂] at e₁
    erw [← HomologicalComplex.cyclesMap_i, reassoc_of% e₁]
    simp only [ShortComplex.SnakeInput.φ₂, Category.assoc]
    exact congrArg (pullback.fst SI.L₁.g SI.v₀₁.τ₃ ≫ ·)
      (HomologicalComplex.opcyclesToCycles_iCycles _ _ _)
  have key := (hS.map_of_exact (Φ.mapHomologicalComplex c)).δ_eq' i j hij _ _ _ h₂ h₁
  rw [reassoc_of% key]
  refine (congrArg (Φ.map SI.φ₁ ≫ ·) ?_).trans (Φ.map_comp _ _).symm
  exact (congrArg (_ ≫ ·) (homologyπ_mapHomologyIso_hom Φ (S.X₁.sc j))).trans
    (Iso.inv_hom_id_assoc _ _)

end ExactFunctorHomology

namespace Ringed

namespace SheafExtContravariant

open RightDerivedComp

/-! ### Arbitrary injective resolutions in the contravariant sequence -/

section AnyResolution

variable {C : Type u'} [Category.{v'} C] [Abelian C] [HasInjectiveResolutions C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.PreservesZeroMorphisms] [∀ F, (H.obj F).Additive]
  (E : C → ℕ → C ⥤ C) (hE : ∀ F n, (H.obj (op F)).rightDerived n = E F n)

/-- The identification of `E F n G` with the cohomology of `H(F, I^•)` for an arbitrary injective
resolution `I^•` of `G`. -/
noncomputable def isoEOf (F : C) {G : C} (I : InjectiveResolution G) (n : ℕ) :
    (E F n).obj G ≅ (((H.obj (op F)).mapHomologicalComplex _).obj I.cocomplex).homology n :=
  eqToIso (Functor.congr_obj (hE F n).symm G) ≪≫ RightDerivedLES.isoH (H.obj (op F)) I n

omit [H.PreservesZeroMorphisms] in
lemma isoE_eq_isoEOf (F G : C) (n : ℕ) :
    isoE H E hE F G n = isoEOf H E hE F (injectiveResolution G) n := rfl

omit [H.PreservesZeroMorphisms] in
/-- Change of injective resolution in `isoEOf`. -/
@[reassoc]
lemma isoEOf_hom_comp_homologyMap (F : C) {G : C} (I J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = J.ι.f 0) (n : ℕ) :
    (isoEOf H E hE F I n).hom ≫
        HomologicalComplex.homologyMap (((H.obj (op F)).mapHomologicalComplex _).map φ) n =
      (isoEOf H E hE F J n).hom := by
  have h := RightDerivedLES.map_comp_isoH_hom (H.obj (op F)) (𝟙 G) I J φ
    (by rw [comm]; exact (Category.id_comp _).symm) n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [isoEOf, isoEOf, Iso.trans_hom, Iso.trans_hom, Category.assoc]
  exact congrArg (_ ≫ ·) h.symm

/-- The short complex of complexes `H(S.X₃, K) ⟶ H(S.X₂, K) ⟶ H(S.X₁, K)` for a cochain
complex `K`. -/
noncomputable abbrev T' (S : ShortComplex C) (K : CochainComplex C ℕ) :
    ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex (H.map S.g.op) _).app K)
    ((NatTrans.mapHomologicalComplex (H.map S.f.op) _).app K) (by
      ext p
      simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.zero_f]
      exact map_g_op_app_comp_map_f_op_app H S _)

/-- The morphism `T'(S, K) ⟶ T'(S, K')` induced by a chain map `K ⟶ K'`. -/
noncomputable def T'map (S : ShortComplex C) {K K' : CochainComplex C ℕ} (φ : K ⟶ K') :
    T' H S K ⟶ T' H S K' where
  τ₁ := ((H.obj (op S.X₃)).mapHomologicalComplex _).map φ
  τ₂ := ((H.obj (op S.X₂)).mapHomologicalComplex _).map φ
  τ₃ := ((H.obj (op S.X₁)).mapHomologicalComplex _).map φ
  comm₁₂ := NatTrans.mapHomologicalComplex_naturality _ _
  comm₂₃ := NatTrans.mapHomologicalComplex_naturality _ _

variable (hH : ∀ (J : C) [Injective J] {S : ShortComplex C} (_ : S.ShortExact),
  (ShortComplex.mk ((H.map S.g.op).app J) ((H.map S.f.op).app J)
    (map_g_op_app_comp_map_f_op_app H S J)).ShortExact)

omit [HasInjectiveResolutions C] in
include hH in
lemma T'_shortExact {S : ShortComplex C} (hS : S.ShortExact) {G : C} (I : InjectiveResolution G) :
    (T' H S I.cocomplex).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    hH (I.cocomplex.X n) hS

/-- **The connecting morphism from any injective resolution.** -/
lemma δ_eq_ofResolution {S : ShortComplex C} (hS : S.ShortExact) {G : C}
    (I : InjectiveResolution G) (n : ℕ) :
    δ H E hE hH hS G n = (isoEOf H E hE S.X₁ I n).hom ≫
      (T'_shortExact H hH hS I).δ n (n + 1) (RightDerivedLES.upRel n) ≫
        (isoEOf H E hE S.X₃ I (n + 1)).inv := by
  let φ := InjectiveResolution.desc (𝟙 G) I (injectiveResolution G)
  have comm : (injectiveResolution G).ι.f 0 ≫ φ.f 0 = I.ι.f 0 := by
    rw [InjectiveResolution.desc_commutes_zero]; exact Category.id_comp _
  have h := HomologicalComplex.HomologySequence.δ_naturality (T'map H S φ)
    (T_shortExact H hH hS G) (T'_shortExact H hH hS I) n (n + 1) (RightDerivedLES.upRel n)
  rw [δ, isoE_eq_isoEOf, isoE_eq_isoEOf, ← isoEOf_hom_comp_homologyMap H E hE S.X₁ _ I φ comm,
    Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  change _ = HomologicalComplex.homologyMap (T'map H S φ).τ₃ n ≫ _ ≫ _
  rw [← reassoc_of% h]
  refine congrArg (_ ≫ ·) ?_
  rw [Iso.eq_comp_inv, ← isoEOf_hom_comp_homologyMap H E hE S.X₃ _ I φ comm, Iso.inv_hom_id_assoc]
  rfl

omit [H.PreservesZeroMorphisms] in
lemma η_app_comp_isoEOf_hom (F : C) {G : C} (I : InjectiveResolution G) :
    (η H E hE F).app G ≫ (isoEOf H E hE F I 0).hom =
      I.toRightDerivedZero' (H.obj (op F)) ≫ (CochainComplex.isoHomologyπ₀ _).hom := by
  rw [η, isoEOf, NatTrans.comp_app, eqToHom_app, Iso.trans_hom, eqToIso.hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    I.toRightDerivedZero_eq (H.obj (op F)), RightDerivedLES.isoH]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AnyResolution

/-! ### Exact functors -/

section ExactFunctor

variable {C : Type u'} [Category.{v'} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u''} [Category.{v''} D] [Abelian D] [HasInjectiveResolutions D]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.PreservesZeroMorphisms] [∀ F, (H.obj F).Additive]
  (E : C → ℕ → C ⥤ C) (hE : ∀ F n, (H.obj (op F)).rightDerived n = E F n)
  (H' : Dᵒᵖ ⥤ D ⥤ D) [H'.PreservesZeroMorphisms] [∀ F, (H'.obj F).Additive]
  (E' : D → ℕ → D ⥤ D) (hE' : ∀ F n, (H'.obj (op F)).rightDerived n = E' F n)
  {Φ : C ⥤ D} [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (hΦ : ∀ I : C, Injective I → Injective (Φ.obj I))
  (α : ∀ F : C, H.obj (op F) ⋙ Φ ≅ Φ ⋙ H'.obj (op (Φ.obj F)))

omit [H.PreservesZeroMorphisms] [H'.PreservesZeroMorphisms] in
lemma rightDerivedCompIsoOf_eq {K : C ⥤ C} [K.Additive] {K' : D ⥤ D} [K'.Additive]
    (e : K ⋙ Φ ≅ Φ ⋙ K') (n : ℕ) (L : C ⥤ C) (hL : K.rightDerived n = L) (L' : D ⥤ D)
    (hL' : K'.rightDerived n = L') {G : C} (I : InjectiveResolution G) :
    rightDerivedCompIsoOf hΦ e n L hL L' hL' G =
      Φ.mapIso (eqToIso (Functor.congr_obj hL.symm G)) ≪≫
        rightDerivedCompIsoOfResolution hΦ e I n ≪≫ eqToIso (Functor.congr_obj hL' (Φ.obj G)) := by
  subst hL hL'
  ext
  simp [rightDerivedCompIsoOf, rightDerivedCompIso_eq_ofResolution hΦ e I]

/-- The isomorphism `Φ(E F n G) ≅ E' (Φ F) n (Φ G)` induced by an exact functor `Φ` preserving
injectives and an identification `α_F : H(F, -) ⋙ Φ ≅ Φ ⋙ H'(Φ F, -)`. -/
noncomputable def extCompIso (F G : C) (n : ℕ) :
    Φ.obj ((E F n).obj G) ≅ (E' (Φ.obj F) n).obj (Φ.obj G) :=
  rightDerivedCompIsoOf hΦ (α F) n (E F n) (hE F n) (E' (Φ.obj F) n) (hE' (Φ.obj F) n) G

omit [H.PreservesZeroMorphisms] [H'.PreservesZeroMorphisms] in
set_option backward.isDefEq.respectTransparency false in
/-- `extCompIso` computed from any injective resolution. -/
lemma extCompIso_hom_eq (F G : C) (I : InjectiveResolution G) (n : ℕ) :
    (extCompIso H E hE H' E' hE' hΦ α F G n).hom = Φ.map (isoEOf H E hE F I n).hom ≫
      (((((H.obj (op F)).mapHomologicalComplex _).obj I.cocomplex).sc n).mapHomologyIso Φ).inv ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (α F).hom _).app I.cocomplex) n ≫
          (isoEOf H' E' hE' (Φ.obj F) (mapInjectiveResolution hΦ I) n).inv := by
  rw [extCompIso, rightDerivedCompIsoOf_eq hΦ (α F) n _ _ _ _ I]
  simp only [rightDerivedCompIsoOfResolution, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    Iso.app_hom, Iso.symm_hom, homologyCompIso_hom_app, isoEOf, Iso.trans_inv, eqToIso.inv,
    RightDerivedLES.isoH, Φ.map_comp, Category.assoc]

variable (hα : ∀ {F' F : C} (f : F' ⟶ F) (G : C),
  Φ.map ((H.map f.op).app G) ≫ (α F').hom.app G =
    (α F).hom.app G ≫ (H'.map (Φ.map f).op).app (Φ.obj G))

include hα in
/-- The morphism of short complexes `Φ(H(S, I)) ⟶ H'(Φ S, Φ I)` given by `α`. -/
noncomputable def Tcomp (S : ShortComplex C) (K : CochainComplex C ℕ) :
    (T' H S K).map (Φ.mapHomologicalComplex _) ⟶
      T' H' (S.map Φ) ((Φ.mapHomologicalComplex _).obj K) where
  τ₁ := (NatTrans.mapHomologicalComplex (α S.X₃).hom _).app K
  τ₂ := (NatTrans.mapHomologicalComplex (α S.X₂).hom _).app K
  τ₃ := (NatTrans.mapHomologicalComplex (α S.X₁).hom _).app K
  comm₁₂ := by
    ext p
    exact (hα S.g (K.X p)).symm
  comm₂₃ := by
    ext p
    exact (hα S.f (K.X p)).symm

variable (hH : ∀ (J : C) [Injective J] {S : ShortComplex C} (_ : S.ShortExact),
    (ShortComplex.mk ((H.map S.g.op).app J) ((H.map S.f.op).app J)
      (map_g_op_app_comp_map_f_op_app H S J)).ShortExact)
  (hH' : ∀ (J : D) [Injective J] {S : ShortComplex D} (_ : S.ShortExact),
    (ShortComplex.mk ((H'.map S.g.op).app J) ((H'.map S.f.op).app J)
      (map_g_op_app_comp_map_f_op_app H' S J)).ShortExact)

include hα in
set_option backward.isDefEq.respectTransparency false in
/-- **The contravariant connecting morphisms commute with an exact functor.** -/
lemma δ_comp_extCompIso {S : ShortComplex C} (hS : S.ShortExact) (G : C) (n : ℕ) :
    Φ.map (δ H E hE hH hS G n) ≫ (extCompIso H E hE H' E' hE' hΦ α S.X₃ G (n + 1)).hom =
      (extCompIso H E hE H' E' hE' hΦ α S.X₁ G n).hom ≫
        δ H' E' hE' hH' (hS.map_of_exact Φ) (Φ.obj G) n := by
  have hT := T'_shortExact H hH hS (injectiveResolution G)
  have h1 := ExactFunctorHomology.δ_map Φ hT n (n + 1) (RightDerivedLES.upRel n)
  have h2 := HomologicalComplex.HomologySequence.δ_naturality (Tcomp H H' α hα S (injectiveResolution G).cocomplex)
    (hT.map_of_exact (Φ.mapHomologicalComplex _))
    (T'_shortExact H' hH' (hS.map_of_exact Φ) (mapInjectiveResolution hΦ (injectiveResolution G))) n (n + 1) (RightDerivedLES.upRel n)
  have key : Φ.map (hT.δ n (n + 1) (RightDerivedLES.upRel n)) ≫
      (((T' H S (injectiveResolution G).cocomplex).X₁.sc (n + 1)).mapHomologyIso Φ).inv ≫
        HomologicalComplex.homologyMap (Tcomp H H' α hα S (injectiveResolution G).cocomplex).τ₁ (n + 1) =
      (((T' H S (injectiveResolution G).cocomplex).X₃.sc n).mapHomologyIso Φ).inv ≫
        HomologicalComplex.homologyMap (Tcomp H H' α hα S (injectiveResolution G).cocomplex).τ₃ n ≫
          (T'_shortExact H' hH' (hS.map_of_exact Φ) (mapInjectiveResolution hΦ (injectiveResolution G))).δ n (n + 1) (RightDerivedLES.upRel n) := by
    rw [← h2, ← Category.assoc, ← Category.assoc]
    refine congrArg (· ≫ _) ?_
    rw [Iso.comp_inv_eq, Category.assoc, h1, Iso.inv_hom_id_assoc]
  rw [δ_eq_ofResolution H' E' hE' hH' (hS.map_of_exact Φ) (mapInjectiveResolution hΦ (injectiveResolution G)) n, δ, isoE_eq_isoEOf,
    isoE_eq_isoEOf, extCompIso_hom_eq _ _ _ _ _ _ _ _ _ _ (injectiveResolution G),
    extCompIso_hom_eq _ _ _ _ _ _ _ _ _ _ (injectiveResolution G)]
  simp only [Functor.map_comp, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  rw [← Φ.map_comp_assoc (isoEOf H E hE S.X₃ (injectiveResolution G) (n + 1)).inv, Iso.inv_hom_id,
    Φ.map_id, Category.id_comp]
  refine congrArg (_ ≫ ·) ?_
  have k2 := congrArg (· ≫ (isoEOf H' E' hE' (Φ.obj S.X₃)
    (mapInjectiveResolution hΦ (injectiveResolution G)) (n + 1)).inv) key
  simp only [Category.assoc] at k2
  exact k2

omit [H.PreservesZeroMorphisms] [H'.PreservesZeroMorphisms] in
set_option backward.isDefEq.respectTransparency false in
/-- **The degree-zero maps `H(F, -) ⟶ E F 0` commute with an exact functor.** -/
lemma η_comp_extCompIso (F G : C) :
    Φ.map ((η H E hE F).app G) ≫ (extCompIso H E hE H' E' hE' hΦ α F G 0).hom =
      (α F).hom.app G ≫ (η H' E' hE' (Φ.obj F)).app (Φ.obj G) := by
  rw [extCompIso_hom_eq _ _ _ _ _ _ _ _ _ _ (injectiveResolution G), ← Φ.map_comp_assoc,
    η_app_comp_isoEOf_hom, ← cancel_mono (isoEOf H' E' hE' (Φ.obj F)
      (mapInjectiveResolution hΦ (injectiveResolution G)) 0).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [η_app_comp_isoEOf_hom]
  have hπ := ExactFunctorHomology.homologyπ_mapHomologyIso_hom Φ
    ((((H.obj (op F)).mapHomologicalComplex _).obj (injectiveResolution G).cocomplex).sc 0)
  have hπ' : Φ.map ((((H.obj (op F)).mapHomologicalComplex _).obj
        (injectiveResolution G).cocomplex).sc 0).homologyπ ≫
      (((((H.obj (op F)).mapHomologicalComplex _).obj
        (injectiveResolution G).cocomplex).sc 0).mapHomologyIso Φ).inv =
      (((((H.obj (op F)).mapHomologicalComplex _).obj
        (injectiveResolution G).cocomplex).sc 0).mapCyclesIso Φ).inv ≫
        (((((H.obj (op F)).mapHomologicalComplex _).obj
          (injectiveResolution G).cocomplex).sc 0).map Φ).homologyπ := by
    rw [Iso.comp_inv_eq, Category.assoc, hπ, Iso.inv_hom_id_assoc]
  rw [Φ.map_comp, Category.assoc]
  erw [reassoc_of% hπ']
  have hn := HomologicalComplex.homologyπ_naturality
    ((NatTrans.mapHomologicalComplex (α F).hom _).app (injectiveResolution G).cocomplex) 0
  refine (congrArg (fun t => Φ.map ((injectiveResolution G).toRightDerivedZero' (H.obj (op F))) ≫
    (((((H.obj (op F)).mapHomologicalComplex _).obj
      (injectiveResolution G).cocomplex).sc 0).mapCyclesIso Φ).inv ≫ t) hn).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  rw [← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ _) ?_
  rw [← cancel_mono (HomologicalComplex.iCycles _ 0)]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  erw [ExactFunctorHomology.mapCyclesIso_inv_iCycles_assoc Φ]
  rw [← Φ.map_comp_assoc]
  erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  erw [(α F).hom.naturality]
  erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  refine congrArg (_ ≫ ·) (congrArg (H'.obj (op (Φ.obj F))).map ?_)
  simp [mapInjectiveResolution]

end ExactFunctor

end SheafExtContravariant

end Ringed

end Hartshorne
