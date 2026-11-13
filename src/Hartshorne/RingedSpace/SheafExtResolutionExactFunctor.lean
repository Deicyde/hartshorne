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

open CategoryTheory Limits Opposite TopologicalSpace

/- The objects of `Φ(K)` for a complex `K` are only definitionally (not reducibly) the images of
the objects of `K`; rewriting along such identifications needs the default transparency. -/
set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace ExactFunctorHomology

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

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

@[reassoc]
lemma map_homologyπ_mapHomologyIso_inv (S : ShortComplex C) :
    Φ.map S.homologyπ ≫ (S.mapHomologyIso Φ).inv = (S.mapCyclesIso Φ).inv ≫ (S.map Φ).homologyπ := by
  rw [Iso.comp_inv_eq, Category.assoc, homologyπ_mapHomologyIso_hom, Iso.inv_hom_id_assoc]

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

open ShortComplex in
@[reassoc]
lemma mapCyclesIso_inv_iCycles (S : ShortComplex C) :
    (S.mapCyclesIso Φ).inv ≫ (S.map Φ).iCycles = Φ.map S.iCycles := by
  rw [← S.mapCyclesIso_hom_iCycles Φ, Iso.inv_hom_id_assoc]

open ShortComplex in
@[reassoc]
lemma mapOpcyclesIso_inv_fromOpcycles (K : HomologicalComplex C c) (i j : ι) :
    ((K.sc i).mapOpcyclesIso Φ).inv ≫ ((Φ.mapHomologicalComplex c).obj K).fromOpcycles i j =
      Φ.map (K.fromOpcycles i j) := by
  have : Epi (Φ.map (K.pOpcycles i)) := Φ.map_epi _
  rw [← cancel_epi (Φ.map (K.pOpcycles i)), ← Φ.map_comp, HomologicalComplex.p_fromOpcycles]
  erw [← pOpcycles_mapOpcyclesIso_hom_assoc Φ (K.sc i), Iso.hom_inv_id_assoc]
  exact ((Φ.mapHomologicalComplex c).obj K).p_fromOpcycles i j

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

omit [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
/-- A reindexing of complexes by `XIsoOfEq` commutes with `Φ` and morphisms out of the images. -/
lemma map_XIsoOfEq_comp {K₁ K₂ : HomologicalComplex C c} {K₁' K₂' : HomologicalComplex D c}
    (c₁ : (Φ.mapHomologicalComplex c).obj K₁ ⟶ K₁') (c₂ : (Φ.mapHomologicalComplex c).obj K₂ ⟶ K₂')
    {a b a' b' : ι} (ha : a = b) (ha' : a' = b') (hX : K₁.X b = K₂.X b')
    (hX' : K₁'.X b = K₂'.X b')
    (hc : c₁.f b ≫ eqToHom hX' = eqToHom (congrArg Φ.obj hX) ≫ c₂.f b') :
    Φ.map ((K₁.XIsoOfEq ha).hom ≫ eqToHom hX ≫ (K₂.XIsoOfEq ha').inv) ≫ c₂.f a' =
      c₁.f a ≫ (K₁'.XIsoOfEq ha).hom ≫ eqToHom hX' ≫ (K₂'.XIsoOfEq ha').inv := by
  subst ha ha'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
    Category.comp_id, eqToHom_map]
  exact hc.symm

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
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  erw [ExactFunctorHomology.mapCyclesIso_inv_iCycles_assoc Φ]
  rw [← Φ.map_comp_assoc]
  erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  erw [(α F).hom.naturality]
  erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  refine congrArg (_ ≫ ·) (congrArg (H'.obj (op (Φ.obj F))).map ?_)
  simp [mapInjectiveResolution]

include hα in
/-- **The first connecting morphism `H(F', G) ⟶ E F'' 1 G` commutes with an exact functor.** -/
lemma homδ_comp_extCompIso {S : ShortComplex C}
    (hS : S.ShortExact) (G : C) :
    Φ.map (homδ H E hE hH hS G) ≫ (extCompIso H E hE H' E' hE' hΦ α S.X₃ G 1).hom =
      (α S.X₁).hom.app G ≫ homδ H' E' hE' hH' (hS.map_of_exact Φ) (Φ.obj G) := by
  rw [homδ, Φ.map_comp_assoc, δ_comp_extCompIso H E hE H' E' hE' hΦ α hα hH hH' hS G 0]
  erw [reassoc_of% (η_comp_extCompIso H E hE H' E' hE' hΦ α S.X₁ G)]
  rfl

end ExactFunctor

end SheafExtContravariant

namespace LocallyFreeResolutionExt

open SheafExtContravariant RightDerivedComp

section ExactFunctor

variable {C : Type u'} [Category.{v'} C] [Abelian C]
  {D : Type u''} [Category.{v''} D] [Abelian D]
  {Φ : C ⥤ D} [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- The image of a resolution under an exact functor. -/
noncomputable def Resolution.map {F : C} (P : Resolution F) (Φ : C ⥤ D) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] : Resolution (Φ.obj F) where
  L := (Φ.mapHomologicalComplex _).obj P.L
  ε := Φ.map P.ε
  w := by
    change Φ.map (P.L.d 1 0) ≫ Φ.map P.ε = 0
    rw [← Φ.map_comp, P.w, Φ.map_zero]
  epi_ε := by
    have := P.epi_ε
    exact Φ.map_epi _
  exact₀ := P.exact₀.map Φ
  exactAt n := (P.exactAt n).map Φ

@[simp]
lemma Resolution.map_L {F : C} (P : Resolution F) :
    (P.map Φ).L = (Φ.mapHomologicalComplex _).obj P.L := rfl

@[simp]
lemma Resolution.map_ε {F : C} (P : Resolution F) : (P.map Φ).ε = Φ.map P.ε := rfl

variable (H : Cᵒᵖ ⥤ C ⥤ C) [H.PreservesZeroMorphisms] (H' : Dᵒᵖ ⥤ D ⥤ D)
  [H'.PreservesZeroMorphisms] (α : ∀ F : C, H.obj (op F) ⋙ Φ ≅ Φ ⋙ H'.obj (op (Φ.obj F)))
  (hα : ∀ {F' F : C} (f : F' ⟶ F) (G : C),
    Φ.map ((H.map f.op).app G) ≫ (α F').hom.app G =
      (α F).hom.app G ≫ (H'.map (Φ.map f).op).app (Φ.obj G))

include hα in
/-- The isomorphism of complexes `Φ(H(L_•, G)) ≅ H'(Φ L_•, Φ G)` given termwise by `α`. -/
noncomputable def homComplexCompIso (L : ChainComplex C ℕ) (G : C) :
    (Φ.mapHomologicalComplex _).obj ((homComplex H L).obj G) ≅
      (homComplex H' ((Φ.mapHomologicalComplex _).obj L)).obj (Φ.obj G) :=
  HomologicalComplex.Hom.isoOfComponents (fun p => (α (L.X p)).app G) (by
    intro p q hpq
    obtain rfl : p + 1 = q := hpq
    change (α (L.X p)).hom.app G ≫
        ((homComplex H' ((Φ.mapHomologicalComplex _).obj L)).obj (Φ.obj G)).d p (p + 1) =
      Φ.map (((homComplex H L).obj G).d p (p + 1)) ≫ (α (L.X (p + 1))).hom.app G
    rw [homComplex_d, homComplex_d]
    exact (hα (L.d (p + 1) p) G).symm)

@[simp]
lemma homComplexCompIso_hom_f (L : ChainComplex C ℕ) (G : C) (p : ℕ) :
    (homComplexCompIso H H' α hα L G).hom.f p = (α (L.X p)).hom.app G := rfl

/-- The isomorphism `Φ(hⁱ(H(L_•, G))) ≅ hⁱ(H'(Φ L_•, Φ G))`. -/
noncomputable def homologyCompIso' (L : ChainComplex C ℕ) (G : C) (i : ℕ) :
    Φ.obj (((homComplex H L).obj G).homology i) ≅
      ((homComplex H' ((Φ.mapHomologicalComplex _).obj L)).obj (Φ.obj G)).homology i :=
  ((((homComplex H L).obj G).sc i).mapHomologyIso Φ).symm ≪≫
    HomologicalComplex.homologyMapIso (homComplexCompIso H H' α hα L G) i

/-- `homologyCompIso'` on cycles. -/
lemma map_homologyπ_comp_homologyCompIso'_hom (L : ChainComplex C ℕ) (G : C) (i : ℕ) :
    Φ.map (((homComplex H L).obj G).homologyπ i) ≫ (homologyCompIso' H H' α hα L G i).hom =
      ((((homComplex H L).obj G).sc i).mapCyclesIso Φ).inv ≫
        HomologicalComplex.cyclesMap (homComplexCompIso H H' α hα L G).hom i ≫
          ((homComplex H' ((Φ.mapHomologicalComplex _).obj L)).obj (Φ.obj G)).homologyπ i := by
  rw [homologyCompIso', Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom]
  erw [ExactFunctorHomology.map_homologyπ_mapHomologyIso_inv_assoc Φ (((homComplex H L).obj G).sc i)]
  exact congrArg (_ ≫ ·)
    (HomologicalComplex.homologyπ_naturality (homComplexCompIso H H' α hα L G).hom i)

lemma mapCyclesIso_inv_cyclesMap_iCycles (L : ChainComplex C ℕ) (G : C) (i : ℕ) :
    ((((homComplex H L).obj G).sc i).mapCyclesIso Φ).inv ≫
        HomologicalComplex.cyclesMap (homComplexCompIso H H' α hα L G).hom i ≫
          ((homComplex H' ((Φ.mapHomologicalComplex _).obj L)).obj (Φ.obj G)).iCycles i =
      Φ.map (((homComplex H L).obj G).iCycles i) ≫ (α (L.X i)).hom.app G := by
  rw [HomologicalComplex.cyclesMap_i]
  erw [ExactFunctorHomology.mapCyclesIso_inv_iCycles_assoc Φ]
  rfl

lemma shiftIso_hom_app {F : C} (P : Resolution F) (n : ℕ) (G : C) :
    (shiftIso H P n).hom.app G = ShortComplex.homologyMap
      ((HomologicalComplex.natIsoSc' C _ n (n + 1) (n + 2) (by simp) (by simp)).hom.app
          ((homComplex H P.truncate.L).obj G) ≫ (scShiftIso H P n).hom.app G ≫
        (HomologicalComplex.natIsoSc' C _ (n + 1) (n + 2) (n + 3) (by simp) (by simp)).inv.app
          ((homComplex H P.L).obj G)) := by
  simp [shiftIso, HomologicalComplex.homologyFunctorIso', HomologicalComplex.homologyFunctorIso,
    ShortComplex.homologyMap_comp]

/-- The reindexing `h^{n+1}(H(L_{•+1}, -)) ≅ h^{n+2}(H(L_•, -))` commutes with `Φ`. -/
lemma shiftIso_comp_homologyCompIso' {F : C} (P : Resolution F) (n : ℕ) (G : C) :
    Φ.map ((shiftIso H P n).hom.app G) ≫ (homologyCompIso' H H' α hα P.L G (n + 2)).hom =
      (homologyCompIso' H H' α hα P.truncate.L G (n + 1)).hom ≫
        (shiftIso H' (P.map Φ) n).hom.app (Φ.obj G) := by
  rw [shiftIso_hom_app, shiftIso_hom_app, homologyCompIso', homologyCompIso', Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom,
    HomologicalComplex.homologyMapIso_hom]
  erw [ShortComplex.mapHomologyIso_inv_naturality_assoc]
  simp only [HomologicalComplex.homologyMap, Category.assoc, ← ShortComplex.homologyMap_comp]
  refine congrArg (_ ≫ ·) ?_
  congr 1
  ext
  · exact ExactFunctorHomology.map_XIsoOfEq_comp Φ
      (homComplexCompIso H H' α hα P.truncate.L G).hom (homComplexCompIso H H' α hα P.L G).hom
      (by simp : (ComplexShape.up ℕ).prev (n + 1) = n)
      (by simp : (ComplexShape.up ℕ).prev (n + 2) = n + 1) rfl rfl
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  · simp [scShiftIso, HomologicalComplex.natIsoSc']
    erw [Category.id_comp, Category.id_comp, Φ.map_id, Category.id_comp, Category.comp_id,
      Category.comp_id]
    rfl
  · exact ExactFunctorHomology.map_XIsoOfEq_comp Φ
      (homComplexCompIso H H' α hα P.truncate.L G).hom (homComplexCompIso H H' α hα P.L G).hom
      (by simp : (ComplexShape.up ℕ).next (n + 1) = n + 2)
      (by simp : (ComplexShape.up ℕ).next (n + 2) = n + 3) rfl rfl
      ((Category.comp_id _).trans (Category.id_comp _).symm)

/-! #### Morphisms from the image of a resolution -/

section Comparison

variable {F : C} {F' : D} (P : Resolution F) (P' : Resolution F') (u : Φ.obj F ⟶ F')
  (ψ : (Φ.mapHomologicalComplex _).obj P.L ⟶ P'.L) (hψ : ψ.f 0 ≫ P'.ε = Φ.map P.ε ≫ u)

include hψ in
lemma kerMap_w : (Φ.map (kernel.ι P.ε) ≫ ψ.f 0) ≫ P'.ε = 0 := by
  rw [Category.assoc]
  erw [hψ]
  rw [← Φ.map_comp_assoc, kernel.condition, Φ.map_zero, zero_comp]

/-- The morphism `Φ(ker(L₀ ⟶ F)) ⟶ ker(L'₀ ⟶ F')` induced by a chain map `Φ L_• ⟶ L'_•` over
`u : Φ F ⟶ F'`. -/
noncomputable def kerMap : Φ.obj (kernel P.ε) ⟶ kernel P'.ε :=
  kernel.lift P'.ε (Φ.map (kernel.ι P.ε) ≫ ψ.f 0) (kerMap_w P P' u ψ hψ)

@[reassoc (attr := simp)]
lemma kerMap_ι : kerMap P P' u ψ hψ ≫ kernel.ι P'.ε = Φ.map (kernel.ι P.ε) ≫ ψ.f 0 :=
  kernel.lift_ι _ _ _

lemma lift_kerMap : ψ.f 1 ≫ P'.lift = Φ.map P.lift ≫ kerMap P P' u ψ hψ := by
  rw [← cancel_mono (kernel.ι P'.ε), Category.assoc, Resolution.lift_ι, Category.assoc, kerMap_ι,
    ← Φ.map_comp_assoc, Resolution.lift_ι]
  exact ψ.comm 1 0

/-- The morphism of short exact sequences `Φ(0 ⟶ K ⟶ L₀ ⟶ F ⟶ 0) ⟶ (0 ⟶ K' ⟶ L'₀ ⟶ F' ⟶ 0)`. -/
@[simps]
noncomputable def sesMap : P.ses.map Φ ⟶ P'.ses where
  τ₁ := kerMap P P' u ψ hψ
  τ₂ := ψ.f 0
  τ₃ := u
  comm₁₂ := kerMap_ι P P' u ψ hψ
  comm₂₃ := hψ

/-- The chain map between the truncated resolutions. -/
noncomputable def truncMap :
    (Φ.mapHomologicalComplex _).obj P.truncate.L ⟶ P'.truncate.L :=
  (ChainComplex.truncate).map ψ

lemma truncMap_comm :
    (truncMap P P' ψ).f 0 ≫ P'.truncate.ε = Φ.map P.truncate.ε ≫ kerMap P P' u ψ hψ :=
  lift_kerMap P P' u ψ hψ

end Comparison

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D] [∀ F, (H.obj F).Additive]
  [∀ F, (H'.obj F).Additive]
  (E : C → ℕ → C ⥤ C) (hE : ∀ F n, (H.obj (op F)).rightDerived n = E F n)
  (E' : D → ℕ → D ⥤ D) (hE' : ∀ F n, (H'.obj (op F)).rightDerived n = E' F n)
  (hΦ : ∀ I : C, Injective I → Injective (Φ.obj I))
  (hH : ∀ (J : C) [Injective J] {S : ShortComplex C} (_ : S.ShortExact),
    (ShortComplex.mk ((H.map S.g.op).app J) ((H.map S.f.op).app J)
      (map_g_op_app_comp_map_f_op_app H S J)).ShortExact)
  (hH' : ∀ (J : D) [Injective J] {S : ShortComplex D} (_ : S.ShortExact),
    (ShortComplex.mk ((H'.map S.g.op).app J) ((H'.map S.f.op).app J)
      (map_g_op_app_comp_map_f_op_app H' S J)).ShortExact)
  [∀ F, PreservesFiniteLimits (H.obj F)] [∀ F, PreservesFiniteLimits (H'.obj F)]

/-- **Resolutions computing `E` and exact functors.** Let `L_• ⟶ F` be a resolution in `C` and
`L'_• ⟶ F'` one in `D`, both with `E`-acyclic terms, and `ψ : Φ L_• ⟶ L'_•` a chain map over
`u : Φ F ⟶ F'`. Then the isomorphisms `E F i ≅ hⁱ(H(L_•, -))` and `E' F' i ≅ hⁱ(H'(L'_•, -))`,
the comparison `Φ(E F i G) ≅ E' (Φ F) i (Φ G)`, the identification
`Φ(hⁱ(H(L_•, G))) ≅ hⁱ(H'(Φ L_•, Φ G))` and the maps induced by `u` and `ψ` form a commutative
square. -/
theorem isoAux_comp (G : C) : ∀ (i : ℕ) {F : C} {F' : D} (P : Resolution F) (P' : Resolution F')
    (u : Φ.obj F ⟶ F') (ψ : (Φ.mapHomologicalComplex _).obj P.L ⟶ P'.L)
    (hψ : ψ.f 0 ≫ P'.ε = Φ.map P.ε ≫ u)
    (hP : ∀ p n G, IsZero ((E (P.L.X p) (n + 1)).obj G))
    (hP' : ∀ p n G, IsZero ((E' (P'.L.X p) (n + 1)).obj G)),
    extMap H' E' hE' u (Φ.obj G) i ≫ (extCompIso H E hE H' E' hE' hΦ α F G i).inv ≫
        Φ.map ((isoAux H E hE hH i P hP).hom.app G) ≫ (homologyCompIso' H H' α hα P.L G i).hom =
      (isoAux H' E' hE' hH' i P' hP').hom.app (Φ.obj G) ≫
        HomologicalComplex.homologyMap ((homComplexMap H' ψ).app (Φ.obj G)) i
  | 0, F, F', P, P', u, ψ, hψ, hP, hP' => by
    have e0 : ∀ {F₀ : C} (Q : Resolution F₀), (η H E hE F₀).app G ≫
        (iso0 H E hE hH Q).hom.app G =
          (cyclesZeroNat H Q).app G ≫ ((homComplex H Q.L).obj G).homologyπ 0 := by
      intro F₀ Q
      rw [iso0_hom]
      simp
    have e0' : ∀ {F₀ : D} (Q : Resolution F₀), (η H' E' hE' F₀).app (Φ.obj G) ≫
        (iso0 H' E' hE' hH' Q).hom.app (Φ.obj G) =
          (cyclesZeroNat H' Q).app (Φ.obj G) ≫
            ((homComplex H' Q.L).obj (Φ.obj G)).homologyπ 0 := by
      intro F₀ Q
      rw [iso0_hom]
      simp
    have h1 : (η H' E' hE' (Φ.obj F)).app (Φ.obj G) ≫
        (extCompIso H E hE H' E' hE' hΦ α F G 0).inv =
          (α F).inv.app G ≫ Φ.map ((η H E hE F).app G) := by
      rw [Iso.comp_inv_eq, Category.assoc, η_comp_extCompIso, Iso.inv_hom_id_app_assoc]
    rw [← cancel_epi ((η H' E' hE' F').app (Φ.obj G)), ← Category.assoc,
      ← map_op_app_comp_η_app, Category.assoc, reassoc_of% h1]
    change _ ≫ _ ≫ Φ.map _ ≫ Φ.map ((iso0 H E hE hH P).hom.app G) ≫ _ =
      (η H' E' hE' F').app (Φ.obj G) ≫ (iso0 H' E' hE' hH' P').hom.app (Φ.obj G) ≫ _
    rw [← Φ.map_comp_assoc, e0, reassoc_of% (e0' P'), Φ.map_comp_assoc,
      map_homologyπ_comp_homologyCompIso'_hom, HomologicalComplex.homologyπ_naturality]
    simp only [← Category.assoc]
    refine congrArg (fun t => t ≫ HomologicalComplex.homologyπ _ 0) ?_
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
    erw [ExactFunctorHomology.mapCyclesIso_inv_iCycles_assoc Φ]
    rw [← Φ.map_comp_assoc]
    have c1 : (cyclesZeroNat H P).app G ≫ ((homComplex H P.L).obj G).iCycles 0 =
        homComplexIn H P.L 0 P.ε G := by
      simp [cyclesZeroNat_app]
    have c2 : (cyclesZeroNat H' P').app (Φ.obj G) ≫
        ((homComplex H' P'.L).obj (Φ.obj G)).iCycles 0 = homComplexIn H' P'.L 0 P'.ε (Φ.obj G) := by
      simp [cyclesZeroNat_app]
    erw [c1]
    rw [reassoc_of% c2, homComplexIn_comp_homComplexMap, homComplexCompIso_hom_f]
    erw [hα P.ε G]
    rw [Iso.inv_hom_id_app_assoc]
    unfold homComplexIn
    rw [map_op_app_comp_map_op_app]
    erw [hψ]
  | 1, F, F', P, P', u, ψ, hψ, hP, hP' => by
    have : Epi (homδ H' E' hE' hH' P'.ses_shortExact (Φ.obj G)) :=
      (hom_exact₁ H' E' hE' hH' P'.ses_shortExact (Φ.obj G)
        (homδ_comp_extMap_g H' E' hE' hH' P'.ses_shortExact (Φ.obj G))).epi_f
          ((hP' 0 0 _).eq_of_tgt _ _)
    have hS := P.ses_shortExact.map_of_exact Φ
    have hn := homδ_naturality H' E' hE' hH' (sesMap P P' u ψ hψ) hS P'.ses_shortExact (Φ.obj G)
    have h1 : homδ H' E' hE' hH' hS (Φ.obj G) ≫ (extCompIso H E hE H' E' hE' hΦ α F G 1).inv =
        (α (kernel P.ε)).inv.app G ≫ Φ.map (homδ H E hE hH P.ses_shortExact G) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      erw [homδ_comp_extCompIso H E hE H' E' hE' hΦ α hα hH hH' P.ses_shortExact G]
      rw [Iso.inv_hom_id_app_assoc]
    rw [← cancel_epi (homδ H' E' hE' hH' P'.ses_shortExact (Φ.obj G)), ← Category.assoc]
    erw [hn]
    rw [Category.assoc, reassoc_of% h1]
    change _ ≫ _ ≫ Φ.map _ ≫ Φ.map ((iso1 H E hE hH P (hP 0 0)).hom.app G) ≫ _ =
      homδ H' E' hE' hH' P'.ses_shortExact (Φ.obj G) ≫
        (iso1 H' E' hE' hH' P' (hP' 0 0)).hom.app (Φ.obj G) ≫ _
    rw [← Φ.map_comp_assoc, homδ_comp_iso1_hom, homδ_comp_iso1_hom_assoc, toHomologyOne_app,
      toHomologyOne_app, Φ.map_comp_assoc, map_homologyπ_comp_homologyCompIso'_hom,
      Category.assoc, HomologicalComplex.homologyπ_naturality]
    simp only [← Category.assoc]
    refine congrArg (fun t => t ≫ HomologicalComplex.homologyπ _ 1) ?_
    rw [← cancel_mono (HomologicalComplex.iCycles _ 1)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
    erw [ExactFunctorHomology.mapCyclesIso_inv_iCycles_assoc Φ]
    rw [← Φ.map_comp_assoc]
    erw [cyclesOneIso_hom_app_iCycles, reassoc_of% (cyclesOneIso_hom_app_iCycles H' hH' P' _)]
    rw [homComplexCompIso_hom_f]
    erw [hα P.lift G]
    rw [Iso.inv_hom_id_app_assoc, homComplexMap_app_f, map_op_app_comp_map_op_app,
      map_op_app_comp_map_op_app, sesMap_τ₁, ← lift_kerMap P P' u ψ hψ]
  | n + 2, F, F', P, P', u, ψ, hψ, hP, hP' => by
    have ih := isoAux_comp G (n + 1) P.truncate P'.truncate (kerMap P P' u ψ hψ)
      (truncMap P P' ψ) (truncMap_comm P P' u ψ hψ) (fun p => hP (p + 1)) (fun p => hP' (p + 1))
    have hs := shiftIso_comp_homologyCompIso' H H' α hα P n G
    have hsn := NatTrans.congr_app
      (shiftIso_naturality H' (⟨ψ, hψ⟩ : Resolution.Hom (P.map Φ) P' u) n) (Φ.obj G)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hsn
    have hS := P.ses_shortExact.map_of_exact Φ
    have hA : extMap H' E' hE' u (Φ.obj G) (n + 2) ≫
        (extCompIso H E hE H' E' hE' hΦ α F G (n + 2)).inv ≫
          Φ.map ((δIso H E hE hH P.ses_shortExact n (hP 0 n) (hP 0 (n + 1))).inv.app G) =
        (δIso H' E' hE' hH' P'.ses_shortExact n (hP' 0 n) (hP' 0 (n + 1))).inv.app (Φ.obj G) ≫
          extMap H' E' hE' (kerMap P P' u ψ hψ) (Φ.obj G) (n + 1) ≫
            (extCompIso H E hE H' E' hE' hΦ α (kernel P.ε) G (n + 1)).inv := by
      rw [← cancel_epi ((δIso H' E' hE' hH' P'.ses_shortExact n (hP' 0 n)
        (hP' 0 (n + 1))).hom.app (Φ.obj G)), Iso.hom_inv_id_app_assoc]
      change δ H' E' hE' hH' P'.ses_shortExact (Φ.obj G) (n + 1) ≫ _ = _
      have hδn := δ_naturality H' E' hE' hH' (sesMap P P' u ψ hψ) hS P'.ses_shortExact
        (Φ.obj G) (n + 1)
      have hc := δ_comp_extCompIso H E hE H' E' hE' hΦ α hα hH hH' P.ses_shortExact G (n + 1)
      have hc' : δ H' E' hE' hH' hS (Φ.obj G) (n + 1) ≫
          (extCompIso H E hE H' E' hE' hΦ α F G (n + 2)).inv =
          (extCompIso H E hE H' E' hE' hΦ α (kernel P.ε) G (n + 1)).inv ≫
            Φ.map (δ H E hE hH P.ses_shortExact G (n + 1)) := by
        rw [Iso.comp_inv_eq, Category.assoc]
        erw [hc]
        rw [Iso.inv_hom_id_assoc]
      rw [← Category.assoc]
      erw [hδn]
      rw [Category.assoc]
      erw [reassoc_of% hc']
      rw [← Φ.map_comp]
      change _ ≫ _ ≫ Φ.map ((δIso H E hE hH P.ses_shortExact n (hP 0 n) (hP 0 (n + 1))).hom.app G ≫
        (δIso H E hE hH P.ses_shortExact n (hP 0 n) (hP 0 (n + 1))).inv.app G) = _
      rw [Iso.hom_inv_id_app, Φ.map_id, Category.comp_id]
      rfl
    simp only [isoAux, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.map_comp,
      Category.assoc]
    erw [reassoc_of% hA]
    rw [hs]
    erw [reassoc_of% ih]
    erw [hsn]
    rfl

end ExactFunctor

end LocallyFreeResolutionExt

/-! ### Sheaf `ℰxt`: restriction to an open subset -/

section Sheaf

open LocallyFreeResolutionExt SheafExtContravariant

attribute [local instance 2000] Abelian.toPreadditive

/-- Injective resolutions of module sheaves, as a single constant (see
`Hartshorne.RingedSpace.SheafExtLongExact`). -/
private theorem sheafOfModules_hasInjectiveResolutions₃ {Y : TopCat.{u}}
    {S : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} :
    HasInjectiveResolutions (SheafOfModules.{u} (ringCatSheafOf S)) :=
  inferInstance

attribute [local instance 3000] sheafOfModules_hasInjectiveResolutions₃

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (U : Opens X)

/-- The identification `ℋom_X(F, G)|_U ≅ ℋom_U(F|_U, G|_U)` is natural in `F`. -/
lemma homRestrict_precomp_naturality {F' F : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F)
    (G : SheafOfModules.{u} (ringCatSheafOf R)) :
    (moduleRestrict U).map ((moduleSheafHomPrecomp f).app G) ≫ homRestrict F' G =
      homRestrict F G ≫ (moduleSheafHomPrecomp ((moduleRestrict U).map f)).app
        ((moduleRestrict U).obj G) := by
  apply SheafOfModules.hom_ext
  ext W σ : 3
  apply SheafOfModules.hom_ext
  ext A x
  rfl

/-- The isomorphism `hⁱ(ℋom_X(L_•, G))|_U ≅ hⁱ(ℋom_U(L_•|_U, G|_U))`. -/
noncomputable def homologyHomComplexRestrictIso (L : ChainComplex (SheafOfModules.{u}
    (ringCatSheafOf R)) ℕ) (G : SheafOfModules.{u} (ringCatSheafOf R)) (i : ℕ) :
    (moduleRestrict U).obj (((moduleSheafHomComplex L).obj G).homology i) ≅
      ((moduleSheafHomComplex (((moduleRestrict U).mapHomologicalComplex _).obj L)).obj
        ((moduleRestrict U).obj G)).homology i :=
  homologyCompIso' (moduleSheafHomBifunctor R) (moduleSheafHomBifunctor (restrictRingSheaf R U))
    (fun F => homRestrictIso U F) (fun f G => homRestrict_precomp_naturality U f G) L G i

-- Matching `sheafExtRestrictIso` and the sheaf-level complexes with their abstract forms unfolds
-- `sheafExt` to the right derived functor it is defined as; this needs more than the default
-- budget.
set_option maxHeartbeats 1000000 in
/-- **The resolution isomorphism restricted to an open subset** (supplementing Hartshorne III.6,
Propositions 6.2 and 6.5). Let `L_• ⟶ F` be a resolution of an `𝒪_X`-module by locally free
`𝒪_X`-modules of finite rank, `L'_• ⟶ F|_U` one of `F|_U` by locally free `𝒪_U`-modules of finite
rank and `ψ : L_•|_U ⟶ L'_•` a chain map over the identity of `F|_U`. Then the restriction to `U`
of `ℰxtⁱ_X(F, G) ≅ hⁱ(ℋom_X(L_•, G))`, read through `ℰxtⁱ_X(F, G)|_U ≅ ℰxtⁱ_U(F|_U, G|_U)` and
`ℋom_X(L_p, G)|_U ≅ ℋom_U(L_p|_U, G|_U)`, is `ℰxtⁱ_U(F|_U, G|_U) ≅ hⁱ(ℋom_U(L'_•, G|_U))` followed
by the map induced by `ψ`. -/
theorem sheafExtIsoHomologyOfLocallyFreeResolution_restrict
    {F : SheafOfModules.{u} (ringCatSheafOf R)} (L : ChainComplex (SheafOfModules.{u}
      (ringCatSheafOf R)) ℕ) (π : L ⟶ (ChainComplex.single₀ _).obj F) [QuasiIso π]
    (hL : ∀ p, IsFiniteLocallyFree (L.X p))
    (L' : ChainComplex (SheafOfModules.{u} (ringCatSheafOf (restrictRingSheaf R U))) ℕ)
    (π' : L' ⟶ (ChainComplex.single₀ _).obj ((moduleRestrict U).obj F)) [QuasiIso π']
    (hL' : ∀ p, IsFiniteLocallyFree (L'.X p))
    (ψ : ((moduleRestrict U).mapHomologicalComplex _).obj L ⟶ L')
    (hψ : ψ.f 0 ≫ π'.f 0 = (moduleRestrict U).map (π.f 0)) (i : ℕ)
    (G : SheafOfModules.{u} (ringCatSheafOf R)) :
    (sheafExtRestrictIso U F G i).inv ≫
        (moduleRestrict U).map ((sheafExtIsoHomologyOfLocallyFreeResolution L π hL i).hom.app G) ≫
          (homologyHomComplexRestrictIso U L G i).hom =
      (sheafExtIsoHomologyOfLocallyFreeResolution L' π' hL' i).hom.app
          ((moduleRestrict U).obj G) ≫
        HomologicalComplex.homologyMap ((moduleSheafHomComplexMap ψ).app _) i := by
  have h := isoAux_comp (Φ := moduleRestrict U) (moduleSheafHomBifunctor R)
    (moduleSheafHomBifunctor (restrictRingSheaf R U)) (fun F => homRestrictIso U F)
    (fun f G => homRestrict_precomp_naturality U f G) sheafExt (fun _ _ => rfl) sheafExt
    (fun _ _ => rfl) (fun I _ => injective_moduleSheafRestrict_obj U (ringCatSheafOf R) I)
    moduleSheafHom_shortExact_of_injective moduleSheafHom_shortExact_of_injective G i
    (Resolution.ofQuasiIso L π) (Resolution.ofQuasiIso L' π') (𝟙 _) ψ
    (hψ.trans (Category.comp_id _).symm)
    (fun p n G => isZero_sheafExt_of_isFiniteLocallyFree (hL p) G n.succ_pos)
    (fun p n G => isZero_sheafExt_of_isFiniteLocallyFree (hL' p) G n.succ_pos)
  rw [extMap_id, Category.id_comp] at h
  unfold sheafExtIsoHomologyOfLocallyFreeResolution moduleSheafHomComplexMap
    homologyHomComplexRestrictIso
  convert h using 2 <;> rfl

end Sheaf


end Ringed

end Hartshorne
