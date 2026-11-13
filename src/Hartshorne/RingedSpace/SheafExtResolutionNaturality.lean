/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtLocallyFreeResolution

/-!
# Naturality of `ℰxtⁱ(F, G) ≅ hⁱ(ℋom(L_•, G))` in the resolution

Let `L_• ⟶ F ⟶ 0` and `L'_• ⟶ F' ⟶ 0` be resolutions by locally free `𝒪_X`-modules of finite rank,
and let `φ : L_• ⟶ L'_•` be a chain map lying over a morphism `u : F ⟶ F'`. Then the isomorphisms
`ℰxtⁱ(F, G) ≅ hⁱ(ℋom(L_•, G))` of Hartshorne III.6, Proposition 6.5, are compatible with the map
`ℰxtⁱ(F', G) ⟶ ℰxtⁱ(F, G)` induced by `u` and the map `hⁱ(ℋom(L'_•, G)) ⟶ hⁱ(ℋom(L_•, G))`
induced by `φ` (`Hartshorne.Ringed.sheafExtIsoHomologyOfLocallyFreeResolution_naturality`). In
particular, for two resolutions of the same `F` and a chain map between them over the identity,
the two identifications of `ℰxtⁱ(F, G)` differ by the map induced on cohomology
(`Hartshorne.Ringed.sheafExtIsoHomologyOfLocallyFreeResolution_comp_homologyMap`).

## Proof

The isomorphisms are built by dimension shifting along `0 ⟶ K ⟶ L₀ ⟶ F ⟶ 0`, `K = ker(L₀ ⟶ F)`,
and induction on the degree. A chain map over `u` induces a morphism `K ⟶ K'` of kernels, hence a
morphism of the two short exact sequences and a chain map between the truncated resolutions
`L_{•+1} ⟶ K` and `L'_{•+1} ⟶ K'` over `K ⟶ K'`. Each step of the construction is then natural:
the identification `ℰxt⁰ = ℋom`, the connecting morphisms of the contravariant long exact
sequence (`Hartshorne.Ringed.SheafExtContravariant.δ_naturality` and `homδ_naturality`), and the
reindexing `h^{n+1}(ℋom(L_{•+1}, G)) ≅ h^{n+2}(ℋom(L_•, G))`. As in
`Hartshorne.RingedSpace.SheafExtLocallyFreeResolution`, this is done for an abstract bifunctor
`H : Cᵒᵖ ⥤ C ⥤ C` and then specialized to `ℋom` and `ℰxt`.
-/

universe u v' u'

open CategoryTheory Limits Opposite

namespace Hartshorne

namespace Ringed

namespace LocallyFreeResolutionExt

open SheafExtContravariant

section Morphisms

variable {C : Type u'} [Category.{v'} C] [Abelian C]

/-- A morphism of resolutions over a morphism `u : F ⟶ F'`: a chain map `L_• ⟶ L'_•` compatible
with the augmentations and `u`. -/
structure Resolution.Hom {F F' : C} (P : Resolution F) (P' : Resolution F') (u : F ⟶ F') where
  /-- The chain map `L_• ⟶ L'_•`. -/
  f : P.L ⟶ P'.L
  /-- Compatibility with the augmentations. -/
  comm : f.f 0 ≫ P'.ε = P.ε ≫ u

namespace Resolution.Hom

variable {F F' : C} {P : Resolution F} {P' : Resolution F'} {u : F ⟶ F'}
  (φ : Resolution.Hom P P' u)

/-- The morphism `ker(L₀ ⟶ F) ⟶ ker(L'₀ ⟶ F')` induced by a morphism of resolutions. -/
noncomputable def kernelMap : kernel P.ε ⟶ kernel P'.ε :=
  kernel.map P.ε P'.ε (φ.f.f 0) u φ.comm.symm

@[reassoc (attr := simp)]
lemma kernelMap_ι : φ.kernelMap ≫ kernel.ι P'.ε = kernel.ι P.ε ≫ φ.f.f 0 :=
  kernel.lift_ι _ _ _

/-- The morphism of short exact sequences `(0 ⟶ K ⟶ L₀ ⟶ F ⟶ 0) ⟶ (0 ⟶ K' ⟶ L'₀ ⟶ F' ⟶ 0)`. -/
@[simps]
noncomputable def ses : P.ses ⟶ P'.ses where
  τ₁ := φ.kernelMap
  τ₂ := φ.f.f 0
  τ₃ := u
  comm₁₂ := φ.kernelMap_ι
  comm₂₃ := φ.comm

lemma lift_kernelMap : P.lift ≫ φ.kernelMap = φ.f.f 1 ≫ P'.lift := by
  rw [← cancel_mono (kernel.ι P'.ε), Category.assoc, kernelMap_ι, Resolution.lift_ι_assoc,
    Category.assoc, Resolution.lift_ι]
  exact (φ.f.comm 1 0).symm

/-- The morphism of truncated resolutions `(L_{•+1} ⟶ K) ⟶ (L'_{•+1} ⟶ K')`. -/
noncomputable def truncate : Resolution.Hom P.truncate P'.truncate φ.kernelMap where
  f := (ChainComplex.truncate).map φ.f
  comm := φ.lift_kernelMap.symm

end Resolution.Hom

end Morphisms

section Abstract

variable {C : Type u'} [Category.{v'} C] [Abelian C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.PreservesZeroMorphisms]

/-- The morphism of cochain complexes `H(L'_•, -) ⟶ H(L_•, -)` induced by a chain map
`L_• ⟶ L'_•`, natural in the second variable. -/
noncomputable def homComplexMap {L L' : ChainComplex C ℕ} (f : L ⟶ L') :
    homComplex H L' ⟶ homComplex H L where
  app G := CochainComplex.ofHom (fun p => (H.map (f.f p).op).app G) (fun p => by
    rw [homComplex_d, homComplex_d]
    refine (map_op_app_comp_map_op_app H _ _ G).trans ?_
    rw [← f.comm]
    exact (map_op_app_comp_map_op_app H _ _ G).symm)
  naturality G G' g := by
    ext p
    exact (H.map (f.f p).op).naturality g

@[simp]
lemma homComplexMap_app_f {L L' : ChainComplex C ℕ} (f : L ⟶ L') (G : C) (p : ℕ) :
    ((homComplexMap H f).app G).f p = (H.map (f.f p).op).app G := rfl

/-- The morphism `H(A, G) ⟶ H(L_p, G)` induced by `f : L_p ⟶ A`, as a morphism into degree `p` of
the complex `H(L_•, G)`. -/
noncomputable def homComplexIn (L : ChainComplex C ℕ) (p : ℕ) {A : C} (f : L.X p ⟶ A) (G : C) :
    (H.obj (op A)).obj G ⟶ ((homComplex H L).obj G).X p :=
  (H.map f.op).app G

lemma homComplexIn_d (L : ChainComplex C ℕ) (p : ℕ) {A : C} (f : L.X p ⟶ A) (G : C) :
    homComplexIn H L p f G ≫ ((homComplex H L).obj G).d p (p + 1) =
      homComplexIn H L (p + 1) (L.d (p + 1) p ≫ f) G := by
  rw [homComplex_d]
  exact map_op_app_comp_map_op_app H _ _ G

lemma homComplexIn_eq_zero (L : ChainComplex C ℕ) (p : ℕ) {A : C} {f : L.X p ⟶ A} (hf : f = 0)
    (G : C) : homComplexIn H L p f G = 0 := by
  subst hf
  exact map_op_app_zero H G

lemma map_comp_homComplexIn (L : ChainComplex C ℕ) (p : ℕ) {A B : C} (f : L.X p ⟶ A)
    (g : A ⟶ B) (G : C) :
    (H.map g.op).app G ≫ homComplexIn H L p f G = homComplexIn H L p (f ≫ g) G :=
  map_op_app_comp_map_op_app H _ _ G

lemma homComplexIn_comp_homComplexMap {L L' : ChainComplex C ℕ} (φ : L ⟶ L') (p : ℕ) {A : C}
    (f : L'.X p ⟶ A) (G : C) :
    homComplexIn H L' p f G ≫ ((homComplexMap H φ).app G).f p =
      homComplexIn H L p (φ.f p ≫ f) G :=
  map_op_app_comp_map_op_app H _ _ G

end Abstract

section Main

variable {C : Type u'} [Category.{v'} C] [Abelian C] [HasInjectiveResolutions C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.PreservesZeroMorphisms] [∀ F, (H.obj F).Additive]
  (E : C → ℕ → C ⥤ C) (hE : ∀ F n, (H.obj (op F)).rightDerived n = E F n)
  (hH : ∀ (J : C) [Injective J] {S : ShortComplex C} (_ : S.ShortExact),
    (ShortComplex.mk ((H.map S.g.op).app J) ((H.map S.f.op).app J)
      (map_g_op_app_comp_map_f_op_app H S J)).ShortExact)
  [∀ F, PreservesFiniteLimits (H.obj F)]
  {F F' : C} {P : Resolution F} {P' : Resolution F'} {u : F ⟶ F'}

omit [H.PreservesZeroMorphisms] [∀ F, PreservesFiniteLimits (H.obj F)] in
/-- The map `E F n ⟶ E F n` induced by the identity of `F` is the identity. -/
lemma extMap_id (F G : C) (n : ℕ) : extMap H E hE (𝟙 F) G n = 𝟙 _ := by
  have h : cmap H (𝟙 F) G = 𝟙 _ := by
    ext p
    simp [cmap]
  rw [extMap_eq, h, HomologicalComplex.homologyMap_id, Category.id_comp, Iso.hom_inv_id]

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] [∀ F, PreservesFiniteLimits (H.obj F)] in
lemma homComplexIn_ε_d (P : Resolution F) (G : C) :
    homComplexIn H P.L 0 P.ε G ≫ ((homComplex H P.L).obj G).d 0 1 = 0 := by
  rw [homComplexIn_d]
  exact homComplexIn_eq_zero H _ _ P.w G

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] [∀ F, PreservesFiniteLimits (H.obj F)] in
/-- Precomposition with `L₀ ⟶ F` as a natural transformation `H(F, -) ⟶ Z⁰(H(L_•, -))`. -/
@[simps]
noncomputable def cyclesZeroNat (P : Resolution F) :
    H.obj (op F) ⟶ homComplex H P.L ⋙ HomologicalComplex.cyclesFunctor C (ComplexShape.up ℕ) 0 where
  app G := ((homComplex H P.L).obj G).liftCycles (homComplexIn H P.L 0 P.ε G) 1 (by simp)
    (homComplexIn_ε_d H P G)
  naturality G G' g := by
    change _ ≫ ((homComplex H P.L).obj G').liftCycles _ 1 (by simp) (homComplexIn_ε_d H P G') =
      ((homComplex H P.L).obj G).liftCycles _ 1 (by simp) (homComplexIn_ε_d H P G) ≫
        HomologicalComplex.cyclesMap ((homComplex H P.L).map g) 0
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0), Category.assoc,
      HomologicalComplex.liftCycles_i, Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i_assoc]
    exact (H.map P.ε.op).naturality g

/-- The degree-zero identification, explicitly: `E F 0 ≅ H(F, -)` followed by the cycles
`H(F, G) ⟶ Z⁰(H(L_•, G))` given by precomposition with `L₀ ⟶ F`. -/
lemma iso0_hom (P : Resolution F) :
    (iso0 H E hE hH P).hom = inv (η H E hE F) ≫ cyclesZeroNat H P ≫
      Functor.whiskerLeft (homComplex H P.L)
        (HomologicalComplex.natTransHomologyπ C (ComplexShape.up ℕ) 0) := by
  rw [← cancel_epi (η H E hE F), IsIso.hom_inv_id_assoc]
  ext G
  simp only [iso0, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  erw [(asIso (η H E hE F)).hom_inv_id_app_assoc]
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  refine eq_whisker ?_ _
  refine (cancel_mono (HomologicalComplex.iCycles _ 0)).1 ?_
  erw [natIsoOfKernels_hom_app_comp, cyclesZeroNat_app, HomologicalComplex.liftCycles_i]
  rfl

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] [∀ F, PreservesFiniteLimits (H.obj F)] in
lemma cyclesZeroNat_naturality (φ : Resolution.Hom P P' u) :
    H.map u.op ≫ cyclesZeroNat H P = cyclesZeroNat H P' ≫
      Functor.whiskerRight (homComplexMap H φ.f)
        (HomologicalComplex.cyclesFunctor C (ComplexShape.up ℕ) 0) := by
  ext G
  change (H.map u.op).app G ≫
      ((homComplex H P.L).obj G).liftCycles _ 1 (by simp) (homComplexIn_ε_d H P G) =
    ((homComplex H P'.L).obj G).liftCycles _ 1 (by simp) (homComplexIn_ε_d H P' G) ≫
      HomologicalComplex.cyclesMap ((homComplexMap H φ.f).app G) 0
  rw [← cancel_mono (HomologicalComplex.iCycles _ 0), Category.assoc,
    HomologicalComplex.liftCycles_i, Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.liftCycles_i_assoc, map_comp_homComplexIn,
    homComplexIn_comp_homComplexMap, φ.comm]

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] [∀ F, PreservesFiniteLimits (H.obj F)] in
/-- The projection onto cohomology commutes with the map induced by a chain map. -/
lemma homologyπ_whisker_naturality {L L' : ChainComplex C ℕ} (f : L ⟶ L') (i : ℕ) (G : C) :
    (Functor.whiskerLeft (homComplex H L')
        (HomologicalComplex.natTransHomologyπ C (ComplexShape.up ℕ) i)).app G ≫
      (Functor.whiskerRight (homComplexMap H f)
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) i)).app G =
    (Functor.whiskerRight (homComplexMap H f)
        (HomologicalComplex.cyclesFunctor C (ComplexShape.up ℕ) i)).app G ≫
      (Functor.whiskerLeft (homComplex H L)
        (HomologicalComplex.natTransHomologyπ C (ComplexShape.up ℕ) i)).app G :=
  ((HomologicalComplex.natTransHomologyπ C (ComplexShape.up ℕ) i).naturality
    ((homComplexMap H f).app G)).symm

lemma iso0_hom_naturality (φ : Resolution.Hom P P' u) (G : C) :
    extMap H E hE u G 0 ≫ (iso0 H E hE hH P).hom.app G =
      (iso0 H E hE hH P').hom.app G ≫ (Functor.whiskerRight (homComplexMap H φ.f)
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) 0)).app G := by
  refine (cancel_epi ((η H E hE F').app G)).1 ?_
  rw [← Category.assoc, ← map_op_app_comp_η_app, Category.assoc, iso0_hom, iso0_hom]
  simp only [NatTrans.comp_app, Category.assoc, NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc]
  rw [homologyπ_whisker_naturality, ← Category.assoc, ← Category.assoc, ← NatTrans.comp_app,
    ← NatTrans.comp_app, cyclesZeroNat_naturality H φ]
  rfl

lemma cyclesOneIso_naturality (φ : Resolution.Hom P P' u) :
    H.map φ.kernelMap.op ≫ (cyclesOneIso H hH P).hom = (cyclesOneIso H hH P').hom ≫
      Functor.whiskerRight (homComplexMap H φ.f)
        (HomologicalComplex.cyclesFunctor C (ComplexShape.up ℕ) 1) := by
  ext G
  rw [NatTrans.comp_app, NatTrans.comp_app]
  refine (cancel_mono (HomologicalComplex.iCycles ((homComplex H P.L).obj G) 1)).1 ?_
  erw [Category.assoc, cyclesOneIso_hom_app_iCycles, Category.assoc,
    HomologicalComplex.cyclesMap_i]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  erw [cyclesOneIso_hom_app_iCycles H hH P' G]
  exact (map_op_app_comp_map_op_app H _ _ G).trans
    ((congrArg (fun f => (H.map f.op).app G) φ.lift_kernelMap).trans
      (map_op_app_comp_map_op_app H _ _ G).symm)

lemma toHomologyOne_naturality (φ : Resolution.Hom P P' u) :
    H.map φ.kernelMap.op ≫ toHomologyOne H hH P = toHomologyOne H hH P' ≫
      Functor.whiskerRight (homComplexMap H φ.f)
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) 1) := by
  ext G
  simp only [toHomologyOne, NatTrans.comp_app, Category.assoc]
  rw [homologyπ_whisker_naturality, ← Category.assoc, ← Category.assoc, ← NatTrans.comp_app,
    ← NatTrans.comp_app, cyclesOneIso_naturality H hH φ]
  rfl

@[reassoc]
lemma homδ_comp_iso1_hom (P : Resolution F) (hP : ∀ G, IsZero ((E (P.L.X 0) 1).obj G)) (G : C) :
    homδ H E hE hH P.ses_shortExact G ≫ (iso1 H E hE hH P hP).hom.app G =
      (toHomologyOne H hH P).app G := by
  have : Epi (homδ H E hE hH P.ses_shortExact G) :=
    (hom_exact₁ H E hE hH P.ses_shortExact G
      (homδ_comp_extMap_g H E hE hH P.ses_shortExact G)).epi_f ((hP G).eq_of_tgt _ _)
  unfold iso1
  exact (hom_exact₃ H E hE hH P.ses_shortExact G
    (map_f_op_app_comp_homδ H E hE hH P.ses_shortExact G)).g_desc _ _

lemma iso1_hom_naturality (φ : Resolution.Hom P P' u) (hP : ∀ G, IsZero ((E (P.L.X 0) 1).obj G))
    (hP' : ∀ G, IsZero ((E (P'.L.X 0) 1).obj G)) (G : C) :
    extMap H E hE u G 1 ≫ (iso1 H E hE hH P hP).hom.app G =
      (iso1 H E hE hH P' hP').hom.app G ≫ (Functor.whiskerRight (homComplexMap H φ.f)
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) 1)).app G := by
  have : Epi (homδ H E hE hH P'.ses_shortExact G) :=
    (hom_exact₁ H E hE hH P'.ses_shortExact G
      (homδ_comp_extMap_g H E hE hH P'.ses_shortExact G)).epi_f ((hP' G).eq_of_tgt _ _)
  have h := homδ_naturality H E hE hH φ.ses P.ses_shortExact P'.ses_shortExact G
  rw [Resolution.Hom.ses_τ₃, Resolution.Hom.ses_τ₁] at h
  refine (cancel_epi (homδ H E hE hH P'.ses_shortExact G)).1 ?_
  rw [← Category.assoc, h, Category.assoc, homδ_comp_iso1_hom, homδ_comp_iso1_hom_assoc,
    ← NatTrans.comp_app, toHomologyOne_naturality H hH φ, NatTrans.comp_app]

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] [∀ F, PreservesFiniteLimits (H.obj F)] in
lemma scShiftIso_naturality (φ : Resolution.Hom P P' u) (n : ℕ) :
    Functor.whiskerRight (homComplexMap H φ.truncate.f)
        (HomologicalComplex.shortComplexFunctor' C _ n (n + 1) (n + 2)) ≫
      (scShiftIso H P n).hom = (scShiftIso H P' n).hom ≫
      Functor.whiskerRight (homComplexMap H φ.f)
        (HomologicalComplex.shortComplexFunctor' C _ (n + 1) (n + 2) (n + 3)) := by
  ext G <;> exact (Category.comp_id _).trans (Category.id_comp _).symm

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] [∀ F, PreservesFiniteLimits (H.obj F)] in
lemma shiftIso_naturality (φ : Resolution.Hom P P' u) (n : ℕ) :
    Functor.whiskerRight (homComplexMap H φ.truncate.f)
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) (n + 1)) ≫
      (shiftIso H P n).hom = (shiftIso H P' n).hom ≫
      Functor.whiskerRight (homComplexMap H φ.f)
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) (n + 2)) := by
  ext G
  simp only [shiftIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp, Iso.symm_hom,
    Category.assoc]
  rw [NatTrans.naturality_assoc, ← NatTrans.naturality, Functor.comp_map, Functor.comp_map,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  have h := NatTrans.congr_app (scShiftIso_naturality H φ n) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  rw [h]

omit [∀ F, PreservesFiniteLimits (H.obj F)] in
lemma δIso_inv_naturality (φ : Resolution.Hom P P' u) (n : ℕ)
    (h₁ : ∀ G, IsZero ((E (P.L.X 0) (n + 1)).obj G))
    (h₂ : ∀ G, IsZero ((E (P.L.X 0) (n + 2)).obj G))
    (h₁' : ∀ G, IsZero ((E (P'.L.X 0) (n + 1)).obj G))
    (h₂' : ∀ G, IsZero ((E (P'.L.X 0) (n + 2)).obj G)) (G : C) :
    extMap H E hE u G (n + 2) ≫ (δIso H E hE hH P.ses_shortExact n h₁ h₂).inv.app G =
      (δIso H E hE hH P'.ses_shortExact n h₁' h₂').inv.app G ≫
        extMap H E hE φ.kernelMap G (n + 1) := by
  have hδ := δ_naturality H E hE hH φ.ses P.ses_shortExact P'.ses_shortExact G (n + 1)
  rw [Resolution.Hom.ses_τ₃, Resolution.Hom.ses_τ₁] at hδ
  have e : ∀ {F₀ : C} (Q : Resolution F₀) (k₁ : ∀ G, IsZero ((E (Q.L.X 0) (n + 1)).obj G))
      (k₂ : ∀ G, IsZero ((E (Q.L.X 0) (n + 2)).obj G)),
      (δIso H E hE hH Q.ses_shortExact n k₁ k₂).hom.app G =
        δ H E hE hH Q.ses_shortExact G (n + 1) := fun _ _ _ => rfl
  rw [← cancel_epi ((δIso H E hE hH P'.ses_shortExact n h₁' h₂').hom.app G),
    Iso.hom_inv_id_app_assoc, e, ← Category.assoc, hδ, Category.assoc, ← e P h₁ h₂,
    Iso.hom_inv_id_app, Category.comp_id]

/-- **Naturality of the dimension-shifting isomorphisms in the resolution.** For resolutions
`L_• ⟶ F` and `L'_• ⟶ F'` with `E`-acyclic terms and a chain map `L_• ⟶ L'_•` over `u : F ⟶ F'`,
the isomorphisms `E F i ≅ hⁱ(H(L_•, -))` and `E F' i ≅ hⁱ(H(L'_•, -))` are compatible with the map
`E F' i ⟶ E F i` induced by `u` and the map on cohomology induced by the chain map. -/
theorem isoAux_hom_naturality (G : C) : ∀ (i : ℕ) {F F' : C} {P : Resolution F}
    {P' : Resolution F'} {u : F ⟶ F'} (φ : Resolution.Hom P P' u)
    (hP : ∀ p n G, IsZero ((E (P.L.X p) (n + 1)).obj G))
    (hP' : ∀ p n G, IsZero ((E (P'.L.X p) (n + 1)).obj G)),
    extMap H E hE u G i ≫ (isoAux H E hE hH i P hP).hom.app G =
      (isoAux H E hE hH i P' hP').hom.app G ≫ (Functor.whiskerRight (homComplexMap H φ.f)
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) i)).app G
  | 0, _, _, _, _, _, φ, _, _ => iso0_hom_naturality H E hE hH φ G
  | 1, _, _, _, _, _, φ, hP, hP' => iso1_hom_naturality H E hE hH φ (hP 0 0) (hP' 0 0) G
  | n + 2, _, _, P, P', u, φ, hP, hP' => by
      have ih := isoAux_hom_naturality G (n + 1) φ.truncate (fun p => hP (p + 1))
        (fun p => hP' (p + 1))
      have hs := NatTrans.congr_app (shiftIso_naturality H φ n) G
      simp only [NatTrans.comp_app] at hs
      simp only [isoAux, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc]
      rw [reassoc_of% (δIso_inv_naturality H E hE hH φ n _ _ (hP' 0 n) (hP' 0 (n + 1)) G),
        reassoc_of% ih, hs]

end Main

end LocallyFreeResolutionExt

/-! ### Sheaf `ℰxt` -/

section Sheaf

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

/- As in `Hartshorne.RingedSpace.SheafExtLocallyFreeResolution`, use the preadditive structure
coming from the abelian structure. -/
attribute [local instance 2000] Abelian.toPreadditive

/-- Injective resolutions of module sheaves, as a single constant. -/
private theorem sheafOfModules_hasInjectiveResolutions'' :
    HasInjectiveResolutions (SheafOfModules.{u} (ringCatSheafOf R)) :=
  inferInstance

attribute [local instance 3000] sheafOfModules_hasInjectiveResolutions''

/-- The morphism of complexes `ℋom(L'_•, G) ⟶ ℋom(L_•, G)` induced by a chain map `L_• ⟶ L'_•` of
`𝒪_X`-modules (precomposition in each degree), natural in `G`. -/
noncomputable def moduleSheafHomComplexMap {L L' : ChainComplex 𝓜 ℕ} (f : L ⟶ L') :
    moduleSheafHomComplex L' ⟶ moduleSheafHomComplex L :=
  LocallyFreeResolutionExt.homComplexMap (moduleSheafHomBifunctor R) f

lemma moduleSheafHomComplexMap_app_f {L L' : ChainComplex 𝓜 ℕ} (f : L ⟶ L') (G : 𝓜) (p : ℕ) :
    ((moduleSheafHomComplexMap f).app G).f p = (moduleSheafHomPrecomp (f.f p)).app G :=
  rfl

/-- **Naturality of `ℰxtⁱ(F, G) ≅ hⁱ(ℋom(L_•, G))` in the resolution** (supplementing Hartshorne
III.6, Proposition 6.5). Let `L_• ⟶ F` and `L'_• ⟶ F'` be resolutions by locally free
`𝒪_X`-modules of finite rank and `φ : L_• ⟶ L'_•` a chain map over `u : F ⟶ F'`. Then the map
`ℰxtⁱ(F', G) ⟶ ℰxtⁱ(F, G)` induced by `u` corresponds, under the isomorphisms of Proposition 6.5,
to the map `hⁱ(ℋom(L'_•, G)) ⟶ hⁱ(ℋom(L_•, G))` induced by `φ`. -/
theorem sheafExtIsoHomologyOfLocallyFreeResolution_naturality {F F' : 𝓜} {u : F ⟶ F'}
    {L L' : ChainComplex 𝓜 ℕ} (π : L ⟶ (ChainComplex.single₀ 𝓜).obj F) [QuasiIso π]
    (π' : L' ⟶ (ChainComplex.single₀ 𝓜).obj F') [QuasiIso π']
    (hL : ∀ p, IsFiniteLocallyFree (L.X p)) (hL' : ∀ p, IsFiniteLocallyFree (L'.X p))
    (φ : L ⟶ L') (hφ : φ ≫ π' = π ≫ (ChainComplex.single₀ 𝓜).map u) (i : ℕ) (G : 𝓜) :
    sheafExtPrecomp u G i ≫ (sheafExtIsoHomologyOfLocallyFreeResolution L π hL i).hom.app G =
      (sheafExtIsoHomologyOfLocallyFreeResolution L' π' hL' i).hom.app G ≫
        (Functor.whiskerRight (moduleSheafHomComplexMap φ)
          (HomologicalComplex.homologyFunctor 𝓜 (ComplexShape.up ℕ) i)).app G := by
  have hc : φ.f 0 ≫ π'.f 0 = π.f 0 ≫ u := by
    have h := HomologicalComplex.congr_hom hφ 0
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at h
    exact h
  exact LocallyFreeResolutionExt.isoAux_hom_naturality (moduleSheafHomBifunctor R) sheafExt
    (fun _ _ => rfl) moduleSheafHom_shortExact_of_injective G i
    (P := LocallyFreeResolutionExt.Resolution.ofQuasiIso L π)
    (P' := LocallyFreeResolutionExt.Resolution.ofQuasiIso L' π') ⟨φ, hc⟩ _ _

/-- **Two locally free resolutions of the same module.** For resolutions `L_• ⟶ F` and
`L'_• ⟶ F` by locally free `𝒪_X`-modules of finite rank and a chain map `φ : L_• ⟶ L'_•` over the
identity of `F`, the two isomorphisms `ℰxtⁱ(F, G) ≅ hⁱ(ℋom(L_•, G))` and
`ℰxtⁱ(F, G) ≅ hⁱ(ℋom(L'_•, G))` of Hartshorne III.6, Proposition 6.5, differ by the map on
cohomology induced by `φ`. -/
theorem sheafExtIsoHomologyOfLocallyFreeResolution_comp_homologyMap {F : 𝓜}
    {L L' : ChainComplex 𝓜 ℕ} (π : L ⟶ (ChainComplex.single₀ 𝓜).obj F) [QuasiIso π]
    (π' : L' ⟶ (ChainComplex.single₀ 𝓜).obj F) [QuasiIso π']
    (hL : ∀ p, IsFiniteLocallyFree (L.X p)) (hL' : ∀ p, IsFiniteLocallyFree (L'.X p))
    (φ : L ⟶ L') (hφ : φ ≫ π' = π) (i : ℕ) (G : 𝓜) :
    (sheafExtIsoHomologyOfLocallyFreeResolution L' π' hL' i).hom.app G ≫
        (Functor.whiskerRight (moduleSheafHomComplexMap φ)
          (HomologicalComplex.homologyFunctor 𝓜 (ComplexShape.up ℕ) i)).app G =
      (sheafExtIsoHomologyOfLocallyFreeResolution L π hL i).hom.app G := by
  have h := sheafExtIsoHomologyOfLocallyFreeResolution_naturality π π' hL hL' φ
    (u := 𝟙 F) (by rw [hφ, CategoryTheory.Functor.map_id, Category.comp_id]) i G
  rw [← h]
  exact (eq_whisker (LocallyFreeResolutionExt.extMap_id _ _ _ F G i) _).trans
    (Category.id_comp _)

end Sheaf

end Ringed

end Hartshorne
