/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.RightDerivedLongExactSequence
import Hartshorne.Cohomology.OpenRestrictionInjective
import Hartshorne.RingedSpace.OpenRestriction
import Hartshorne.RingedSpace.SheafExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The contravariant long exact sequence of sheaf `ℰxt`

Hartshorne, *Algebraic Geometry*, III.6, Proposition 6.4 (p. 234).

Let `(X, 𝒪_X)` be a ringed space, `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` a short exact sequence of
`𝒪_X`-modules and `G` an `𝒪_X`-module. There is a natural long exact sequence

`0 ⟶ ℋom(F'', G) ⟶ ℋom(F, G) ⟶ ℋom(F', G) ⟶ ℰxt¹(F'', G) ⟶ ℰxt¹(F, G) ⟶ ℰxt¹(F', G) ⟶ ⋯`
`⋯ ⟶ ℰxtⁿ(F'', G) ⟶ ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F', G) ⟶ ℰxtⁿ⁺¹(F'', G) ⟶ ⋯`.

The maps `ℋom(F, G) ⟶ ℋom(F', G)` are precomposition (`Hartshorne.Ringed.moduleSheafHomPrecomp`),
which makes `ℋom` a bifunctor (`Hartshorne.Ringed.moduleSheafHomBifunctor`); the maps
`ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F', G)` (`Hartshorne.Ringed.sheafExtPrecomp`) are the induced morphisms of right
derived functors. Following Hartshorne, for an injective `𝒪_X`-module `J` the functor `ℋom(-, J)`
is exact (`Hartshorne.Ringed.moduleSheafHom_shortExact_of_injective`): on sections over an open
`U` it is `Hom(-|_U, J|_U)`, and `J|_U` is injective by Lemma 6.1
(`Hartshorne.Ringed.injective_over`). Hence for an injective resolution `G ⟶ I^•` the sequence
of complexes `0 ⟶ ℋom(F'', I^•) ⟶ ℋom(F, I^•) ⟶ ℋom(F', I^•) ⟶ 0` is short exact, and its
cohomology sequence gives the connecting morphisms `Hartshorne.Ringed.sheafExtContraδ` and, in
degree zero, `Hartshorne.Ringed.sheafHomContraδ`. Exactness at every spot is
`Hartshorne.Ringed.sheafHom_contra_mono`, `Hartshorne.Ringed.sheafHom_contra_exact₂`,
`Hartshorne.Ringed.sheafHom_contra_exact₃`, `Hartshorne.Ringed.sheafHom_contra_exact₁`,
`Hartshorne.Ringed.sheafExt_contra_exact₂`, `Hartshorne.Ringed.sheafExt_contra_exact₃` and
`Hartshorne.Ringed.sheafExt_contra_exact₁`; naturality in morphisms of short exact sequences is
`Hartshorne.Ringed.sheafHomContraδ_naturality` and `Hartshorne.Ringed.sheafExtContraδ_naturality`.

## Implementation note

The homological algebra is done for an abstract bifunctor `H : Cᵒᵖ ⥤ C ⥤ C` on an abelian
category and a family of functors `E F n` equal to the right derived functors of `H(F, -)`
(namespace `Hartshorne.Ringed.SheafExtContravariant`), and then specialized to `ℋom` and
`ℰxt`. As in `Hartshorne.RingedSpace.SheafExtLongExact`, the additivity of `ℋom(F, -)` and the
existence of injective resolutions are restated once as local instances so that the kernel does
not compare differently elaborated instance arguments.
-/

universe u v' u'

open CategoryTheory Limits Opposite TopologicalSpace

namespace Hartshorne

namespace Ringed

namespace SheafExtContravariant

/-! ### The long exact sequence in the first variable, for an abstract bifunctor

Let `H : Cᵒᵖ ⥤ C ⥤ C` be a functor such that each `H(F, -)` is additive and `H(-, J)` sends short
exact sequences to short exact sequences when `J` is injective, and let `E F n` be functors equal
to the right derived functors of `H(F, -)`. A short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` gives,
for an injective resolution `G ⟶ I^•`, a short exact sequence of complexes
`0 ⟶ H(F'', I^•) ⟶ H(F, I^•) ⟶ H(F', I^•) ⟶ 0`, whose homology sequence is a long exact sequence
`⋯ ⟶ E F'' n G ⟶ E F n G ⟶ E F' n G ⟶ E F'' (n + 1) G ⟶ ⋯`. -/

variable {C : Type u'} [Category.{v'} C] [Abelian C] [HasInjectiveResolutions C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.PreservesZeroMorphisms] [∀ F, (H.obj F).Additive]
  (E : C → ℕ → C ⥤ C) (hE : ∀ F n, (H.obj (op F)).rightDerived n = E F n)

/-- The chain map `H(F, I^•) ⟶ H(F', I^•)` induced by `f : F' ⟶ F`. -/
noncomputable abbrev cmap {F' F : C} (f : F' ⟶ F) (G : C) :
    ((H.obj (op F)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution G).cocomplex ⟶
      ((H.obj (op F')).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution G).cocomplex :=
  (NatTrans.mapHomologicalComplex (H.map f.op) _).app _

omit [Abelian C] [HasInjectiveResolutions C] [H.PreservesZeroMorphisms] [∀ F, (H.obj F).Additive] in
lemma map_op_app_comp_map_op_app {F'' F F' : C} (f : F' ⟶ F) (g : F ⟶ F'') (X : C) :
    (H.map g.op).app X ≫ (H.map f.op).app X = (H.map (f ≫ g).op).app X := by
  rw [← NatTrans.comp_app, ← H.map_comp, ← op_comp]

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] in
lemma map_op_app_zero {F' F : C} (X : C) : (H.map (0 : F' ⟶ F).op).app X = 0 := by
  rw [op_zero, H.map_zero, NatTrans.app_zero]

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] in
lemma map_g_op_app_comp_map_f_op_app (S : ShortComplex C) (X : C) :
    (H.map S.g.op).app X ≫ (H.map S.f.op).app X = 0 := by
  rw [map_op_app_comp_map_op_app, S.zero, map_op_app_zero]

omit [H.PreservesZeroMorphisms] in
lemma cmap_comp {F'' F F' : C} (f : F' ⟶ F) (g : F ⟶ F'') (G : C) :
    cmap H g G ≫ cmap H f G = cmap H (f ≫ g) G := by
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
  exact map_op_app_comp_map_op_app H f g _

lemma cmap_zero {F' F : C} (G : C) : cmap H (0 : F' ⟶ F) G = 0 := by
  ext n
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.zero_f]
  exact map_op_app_zero H _

/-- The short complex of complexes `H(S.X₃, I^•) ⟶ H(S.X₂, I^•) ⟶ H(S.X₁, I^•)`. -/
noncomputable abbrev T (S : ShortComplex C) (G : C) : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (cmap H S.g G) (cmap H S.f G) (by rw [cmap_comp, S.zero, cmap_zero])

/-- The identification of `E F n G` with the cohomology of `H(F, I^•)` for the chosen injective
resolution `I^•` of `G`. -/
noncomputable def isoE (F G : C) (n : ℕ) :
    (E F n).obj G ≅ (((H.obj (op F)).mapHomologicalComplex _).obj
      (injectiveResolution G).cocomplex).homology n :=
  eqToIso (Functor.congr_obj (hE F n).symm G) ≪≫
    RightDerivedLES.isoH (H.obj (op F)) (injectiveResolution G) n

/-- The map `E F n G ⟶ E F' n G` induced by `f : F' ⟶ F`: Mathlib's natural transformation
between right derived functors induced by `H(f, -)`, transported along the equalities. -/
noncomputable def extMap {F' F : C} (f : F' ⟶ F) (G : C) (n : ℕ) :
    (E F n).obj G ⟶ (E F' n).obj G :=
  eqToHom (Functor.congr_obj (hE F n).symm G) ≫ (NatTrans.rightDerived (H.map f.op) n).app G ≫
    eqToHom (Functor.congr_obj (hE F' n) G)

omit [H.PreservesZeroMorphisms] in
@[reassoc]
lemma extMap_comp_isoE_hom {F' F : C} (f : F' ⟶ F) (G : C) (n : ℕ) :
    extMap H E hE f G n ≫ (isoE H E hE F' G n).hom =
      (isoE H E hE F G n).hom ≫ HomologicalComplex.homologyMap (cmap H f G) n := by
  rw [extMap, isoE, isoE, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom,
    InjectiveResolution.rightDerived_app_eq (H.map f.op) (injectiveResolution G) n]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    RightDerivedLES.isoH]
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

omit [H.PreservesZeroMorphisms] in
lemma extMap_eq {F' F : C} (f : F' ⟶ F) (G : C) (n : ℕ) :
    extMap H E hE f G n = (isoE H E hE F G n).hom ≫
      HomologicalComplex.homologyMap (cmap H f G) n ≫ (isoE H E hE F' G n).inv := by
  rw [← extMap_comp_isoE_hom_assoc, Iso.hom_inv_id, Category.comp_id]

omit [H.PreservesZeroMorphisms] in
lemma extMap_comp {F'' F F' : C} (f : F' ⟶ F) (g : F ⟶ F'') (G : C) (n : ℕ) :
    extMap H E hE g G n ≫ extMap H E hE f G n = extMap H E hE (f ≫ g) G n := by
  simp only [extMap_eq, Category.assoc, Iso.inv_hom_id_assoc,
    ← HomologicalComplex.homologyMap_comp_assoc,
    cmap_comp]

lemma extMap_zero {F' F : C} (G : C) (n : ℕ) : extMap H E hE (0 : F' ⟶ F) G n = 0 := by
  simp [extMap_eq, cmap_zero]

lemma extMap_g_comp_extMap_f (S : ShortComplex C) (G : C) (n : ℕ) :
    extMap H E hE S.g G n ≫ extMap H E hE S.f G n = 0 := by
  rw [extMap_comp, S.zero, extMap_zero]

variable (hH : ∀ (J : C) [Injective J] {S : ShortComplex C} (_ : S.ShortExact),
  (ShortComplex.mk ((H.map S.g.op).app J) ((H.map S.f.op).app J)
    (map_g_op_app_comp_map_f_op_app H S J)).ShortExact)

include hH in
lemma T_shortExact {S : ShortComplex C} (hS : S.ShortExact) (G : C) : (T H S G).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    hH ((injectiveResolution G).cocomplex.X n) hS

/-- The connecting morphism `E F' n G ⟶ E F'' (n + 1) G` of a short exact sequence
`0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0`. -/
noncomputable def δ {S : ShortComplex C} (hS : S.ShortExact) (G : C) (n : ℕ) :
    (E S.X₁ n).obj G ⟶ (E S.X₃ (n + 1)).obj G :=
  (isoE H E hE S.X₁ G n).hom ≫ (T_shortExact H hH hS G).δ n (n + 1) (RightDerivedLES.upRel n) ≫
    (isoE H E hE S.X₃ G (n + 1)).inv

lemma extMap_f_comp_δ {S : ShortComplex C} (hS : S.ShortExact) (G : C) (n : ℕ) :
    extMap H E hE S.f G n ≫ δ H E hE hH hS G n = 0 := by
  have h := (T_shortExact H hH hS G).comp_δ n (n + 1) (RightDerivedLES.upRel n)
  simp only [extMap_eq, δ, Category.assoc, Iso.inv_hom_id_assoc]
  erw [reassoc_of% h]
  rw [zero_comp, comp_zero]

lemma δ_comp_extMap_g {S : ShortComplex C} (hS : S.ShortExact) (G : C) (n : ℕ) :
    δ H E hE hH hS G n ≫ extMap H E hE S.g G (n + 1) = 0 := by
  have h := (T_shortExact H hH hS G).δ_comp n (n + 1) (RightDerivedLES.upRel n)
  simp only [extMap_eq, δ, Category.assoc, Iso.inv_hom_id_assoc]
  erw [reassoc_of% h]
  rw [zero_comp, comp_zero]

include hH in
lemma exact₂ {S : ShortComplex C} (hS : S.ShortExact) (G : C) (n : ℕ)
    (w : extMap H E hE S.g G n ≫ extMap H E hE S.f G n = 0) :
    (ShortComplex.mk (extMap H E hE S.g G n) (extMap H E hE S.f G n) w).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((T_shortExact H hH hS G).homology_exact₂ n)
  exact ShortComplex.isoMk (isoE H E hE S.X₃ G n) (isoE H E hE S.X₂ G n) (isoE H E hE S.X₁ G n)
    (extMap_comp_isoE_hom H E hE S.g G n).symm (extMap_comp_isoE_hom H E hE S.f G n).symm

lemma exact₃ {S : ShortComplex C} (hS : S.ShortExact) (G : C) (n : ℕ)
    (w : extMap H E hE S.f G n ≫ δ H E hE hH hS G n = 0) :
    (ShortComplex.mk (extMap H E hE S.f G n) (δ H E hE hH hS G n) w).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2
    ((T_shortExact H hH hS G).homology_exact₃ n (n + 1) (RightDerivedLES.upRel n))
  exact ShortComplex.isoMk (isoE H E hE S.X₂ G n) (isoE H E hE S.X₁ G n)
    (isoE H E hE S.X₃ G (n + 1)) (extMap_comp_isoE_hom H E hE S.f G n).symm (by simp [δ])

lemma exact₁ {S : ShortComplex C} (hS : S.ShortExact) (G : C) (n : ℕ)
    (w : δ H E hE hH hS G n ≫ extMap H E hE S.g G (n + 1) = 0) :
    (ShortComplex.mk (δ H E hE hH hS G n) (extMap H E hE S.g G (n + 1)) w).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2
    ((T_shortExact H hH hS G).homology_exact₁ n (n + 1) (RightDerivedLES.upRel n))
  exact ShortComplex.isoMk (isoE H E hE S.X₁ G n) (isoE H E hE S.X₃ G (n + 1))
    (isoE H E hE S.X₂ G (n + 1)) (by simp [δ]) (extMap_comp_isoE_hom H E hE S.g G (n + 1)).symm

/-- The morphism of short complexes of complexes induced by a morphism of short complexes, in the
contravariant direction. -/
noncomputable def Tmap {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (G : C) : T H S₂ G ⟶ T H S₁ G where
  τ₁ := cmap H φ.τ₃ G
  τ₂ := cmap H φ.τ₂ G
  τ₃ := cmap H φ.τ₁ G
  comm₁₂ := by
    change cmap H φ.τ₃ G ≫ cmap H S₁.g G = cmap H S₂.g G ≫ cmap H φ.τ₂ G
    rw [cmap_comp, cmap_comp, φ.comm₂₃]
  comm₂₃ := by
    change cmap H φ.τ₂ G ≫ cmap H S₁.f G = cmap H S₂.f G ≫ cmap H φ.τ₁ G
    rw [cmap_comp, cmap_comp, φ.comm₁₂]

lemma δ_naturality {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (G : C) (n : ℕ) :
    δ H E hE hH hS₂ G n ≫ extMap H E hE φ.τ₃ G (n + 1) =
      extMap H E hE φ.τ₁ G n ≫ δ H E hE hH hS₁ G n := by
  have h := HomologicalComplex.HomologySequence.δ_naturality (Tmap H φ G)
    (T_shortExact H hH hS₂ G) (T_shortExact H hH hS₁ G) n (n + 1) (RightDerivedLES.upRel n)
  simp only [extMap_eq, δ, Category.assoc, Iso.inv_hom_id_assoc]
  change _ ≫ _ ≫ HomologicalComplex.homologyMap (Tmap H φ G).τ₁ (n + 1) ≫ _ =
    _ ≫ HomologicalComplex.homologyMap (Tmap H φ G).τ₃ n ≫ _
  rw [reassoc_of% h]

/-! ### Degree zero -/

/-- The canonical map `H(F, -) ⟶ E F 0`, transported from `H(F, -) ⟶ R⁰H(F, -)`. -/
noncomputable def η (F : C) : H.obj (op F) ⟶ E F 0 :=
  (H.obj (op F)).toRightDerivedZero ≫ eqToHom (hE F 0)

omit [HasInjectiveResolutions C] [H.PreservesZeroMorphisms] in
@[reassoc]
lemma toRightDerivedZero'_natTrans {F G : C ⥤ C} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C}
    (P : InjectiveResolution X) :
    α.app X ≫ P.toRightDerivedZero' G =
      P.toRightDerivedZero' F ≫ HomologicalComplex.cyclesMap
        ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) 0 := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ _), Category.assoc, Category.assoc,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles, HomologicalComplex.cyclesMap_i]
  erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
  exact (α.naturality _).symm

omit [H.PreservesZeroMorphisms] in
lemma η_app_comp_isoE_hom (F G : C) :
    (η H E hE F).app G ≫ (isoE H E hE F G 0).hom =
      (injectiveResolution G).toRightDerivedZero' (H.obj (op F)) ≫
        (CochainComplex.isoHomologyπ₀ _).hom := by
  rw [η, isoE, NatTrans.comp_app, eqToHom_app, Iso.trans_hom, eqToIso.hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    (injectiveResolution G).toRightDerivedZero_eq (H.obj (op F)), RightDerivedLES.isoH]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [H.PreservesZeroMorphisms] in
lemma map_op_app_comp_η_app {F' F : C} (f : F' ⟶ F) (G : C) :
    (H.map f.op).app G ≫ (η H E hE F').app G = (η H E hE F).app G ≫ extMap H E hE f G 0 := by
  rw [← cancel_mono (isoE H E hE F' G 0).hom, Category.assoc, Category.assoc,
    extMap_comp_isoE_hom, η_app_comp_isoE_hom, reassoc_of% η_app_comp_isoE_hom,
    toRightDerivedZero'_natTrans_assoc]
  congr 1
  exact (HomologicalComplex.homologyπ_naturality (cmap H f G) 0).symm

/-- The connecting morphism `H(F', G) ⟶ E F'' 1 G`. -/
noncomputable def homδ {S : ShortComplex C} (hS : S.ShortExact) (G : C) :
    (H.obj (op S.X₁)).obj G ⟶ (E S.X₃ 1).obj G :=
  (η H E hE S.X₁).app G ≫ δ H E hE hH hS G 0

lemma map_f_op_app_comp_homδ {S : ShortComplex C} (hS : S.ShortExact) (G : C) :
    (H.map S.f.op).app G ≫ homδ H E hE hH hS G = 0 := by
  rw [homδ, ← Category.assoc, map_op_app_comp_η_app, Category.assoc, extMap_f_comp_δ, comp_zero]

lemma homδ_comp_extMap_g {S : ShortComplex C} (hS : S.ShortExact) (G : C) :
    homδ H E hE hH hS G ≫ extMap H E hE S.g G 1 = 0 := by
  rw [homδ, Category.assoc, δ_comp_extMap_g, comp_zero]

lemma homδ_naturality {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (G : C) :
    homδ H E hE hH hS₂ G ≫ extMap H E hE φ.τ₃ G 1 =
      (H.map φ.τ₁.op).app G ≫ homδ H E hE hH hS₁ G := by
  rw [homδ, homδ, Category.assoc, δ_naturality H E hE hH φ hS₁ hS₂ G 0, ← Category.assoc,
    ← Category.assoc, map_op_app_comp_η_app]

omit [H.PreservesZeroMorphisms] in
/-- The right derived functors of the functors `H(F, -)`. -/
noncomputable abbrev rd (F : C) (n : ℕ) : C ⥤ C := (H.obj (op F)).rightDerived n

variable [∀ F, PreservesFiniteLimits (H.obj F)]

instance (F : C) : IsIso (η H E hE F) := by
  dsimp [η]; infer_instance

include hH in
lemma hom_mono {S : ShortComplex C} (hS : S.ShortExact) (G : C) :
    Mono ((H.map S.g.op).app G) := by
  have hT := T_shortExact H hH hS G
  have := hT.mono_f
  have : Mono (HomologicalComplex.homologyMap (T H S G).f 0) := by
    have : Mono (HomologicalComplex.homologyMap (T H S G).f 0 ≫
        (CochainComplex.isoHomologyπ₀ (T H S G).X₂).inv) := by
      rw [CochainComplex.isoHomologyπ₀_inv_naturality]
      infer_instance
    exact mono_of_mono _ (CochainComplex.isoHomologyπ₀ (T H S G).X₂).inv
  have : Mono (extMap H (rd H) (fun _ _ ↦ rfl) S.g G 0) := by
    rw [extMap_eq]
    change Mono (_ ≫ HomologicalComplex.homologyMap (T H S G).f 0 ≫ _)
    infer_instance
  have : Mono ((H.map S.g.op).app G ≫ (η H (rd H) (fun _ _ ↦ rfl) S.X₂).app G) := by
    rw [map_op_app_comp_η_app]; infer_instance
  exact mono_of_mono _ ((η H (rd H) (fun _ _ ↦ rfl) S.X₂).app G)

include hH in
lemma hom_exact₂ {S : ShortComplex C} (hS : S.ShortExact) (G : C)
    (w : (H.map S.g.op).app G ≫ (H.map S.f.op).app G = 0) :
    (ShortComplex.mk ((H.map S.g.op).app G) ((H.map S.f.op).app G) w).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2
    (exact₂ H (rd H) (fun _ _ ↦ rfl) hH hS G 0
      (extMap_g_comp_extMap_f H (rd H) (fun _ _ ↦ rfl) S G 0))
  exact ShortComplex.isoMk (asIso ((η H (rd H) (fun _ _ ↦ rfl) S.X₃).app G))
    (asIso ((η H (rd H) (fun _ _ ↦ rfl) S.X₂).app G))
    (asIso ((η H (rd H) (fun _ _ ↦ rfl) S.X₁).app G))
    (map_op_app_comp_η_app H (rd H) (fun _ _ ↦ rfl) S.g G).symm
    (map_op_app_comp_η_app H (rd H) (fun _ _ ↦ rfl) S.f G).symm

lemma hom_exact₃ {S : ShortComplex C} (hS : S.ShortExact) (G : C)
    (w : (H.map S.f.op).app G ≫ homδ H E hE hH hS G = 0) :
    (ShortComplex.mk ((H.map S.f.op).app G) (homδ H E hE hH hS G) w).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2
    (exact₃ H E hE hH hS G 0 (extMap_f_comp_δ H E hE hH hS G 0))
  exact ShortComplex.isoMk (asIso ((η H E hE S.X₂).app G)) (asIso ((η H E hE S.X₁).app G))
    (Iso.refl _) (map_op_app_comp_η_app H E hE S.f G).symm (by simp [homδ])

lemma hom_exact₁ {S : ShortComplex C} (hS : S.ShortExact) (G : C)
    (w : homδ H E hE hH hS G ≫ extMap H E hE S.g G 1 = 0) :
    (ShortComplex.mk (homδ H E hE hH hS G) (extMap H E hE S.g G 1) w).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2
    (exact₁ H E hE hH hS G 0 (δ_comp_extMap_g H E hE hH hS G 0))
  exact ShortComplex.isoMk (asIso ((η H E hE S.X₁).app G)) (Iso.refl _) (Iso.refl _)
    (by simp [homδ]) (by simp)

end SheafExtContravariant

/-! ### Sheaf Hom in the first variable -/

section ModuleSheafHom

open SheafOfModules (Hom.over)

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- **Injectives restrict to injectives** (Hartshorne III.6, Lemma 6.1), for the restriction
`J ↦ J|_U` to the opens contained in `U` that defines the sheaf Hom: through Mathlib's
equivalence with module sheaves on the subspace `U`, it is the restriction of
`Hartshorne.injective_moduleSheafRestrict_obj`. -/
theorem injective_over (J : SheafOfModules.{u} (ringCatSheafOf R)) [Injective J] (U : Opens X) :
    Injective (J.over U) := by
  let e := U.sheafOfModulesEquivOver (ringCatSheafOf R)
  have h₁ : Injective (e.functor.obj (J.over U)) :=
    injective_moduleSheafRestrict_obj U (ringCatSheafOf R) J
  have h₂ : Injective (e.inverse.obj (e.functor.obj (J.over U))) :=
    Injective.injective_of_adjoint e.toAdjunction _
  exact Injective.of_iso (e.unitIso.app (J.over U)).symm h₂

/-- The morphism `ℋom(F, G) ⟶ ℋom(F', G)` given by precomposition with `f : F' ⟶ F`, natural in
`G`. -/
noncomputable def moduleSheafHomPrecomp {F' F : SheafOfModules.{u} (ringCatSheafOf R)}
    (f : F' ⟶ F) : moduleSheafHomFunctor F ⟶ moduleSheafHomFunctor F' where
  app G := moduleSheafHomMap f (𝟙 G)
  naturality {G G'} g := by
    apply SheafOfModules.hom_ext
    ext U σ
    change Hom.over (𝟙 F') U.unop ≫
        (Hom.over f U.unop ≫ σ ≫ Hom.over (𝟙 G) U.unop) ≫ Hom.over g U.unop =
      Hom.over f U.unop ≫
        (Hom.over (𝟙 F) U.unop ≫ σ ≫ Hom.over g U.unop) ≫ Hom.over (𝟙 G') U.unop
    obtain ⟨τ, rfl⟩ : ∃ τ : F.over U.unop ⟶ G.over U.unop, τ = σ := ⟨σ, rfl⟩
    simp

/-- On sections over `U`, precomposition with `f` is precomposition with `f|_U`. -/
lemma moduleSheafHomPrecomp_app_app {F' F : SheafOfModules.{u} (ringCatSheafOf R)}
    (f : F' ⟶ F) (G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X)
    (σ : (moduleSheafHom F G).val.obj (op U)) :
    moduleSheafHomOverSectionsAddEquiv F' G U (((moduleSheafHomPrecomp f).app G).val.app (op U) σ) =
      Hom.over f U ≫ moduleSheafHomOverSectionsAddEquiv F G U σ := by
  change Hom.over f U ≫ σ ≫ Hom.over (𝟙 G) U =
    Hom.over f U ≫ σ
  obtain ⟨τ, rfl⟩ : ∃ τ : F.over U ⟶ G.over U, τ = σ := ⟨σ, rfl⟩
  simp

variable (R) in
/-- The sheaf Hom bifunctor `(F, G) ↦ ℋom(F, G)`, contravariant in `F`. -/
noncomputable def moduleSheafHomBifunctor :
    (SheafOfModules.{u} (ringCatSheafOf R))ᵒᵖ ⥤
      SheafOfModules.{u} (ringCatSheafOf R) ⥤ SheafOfModules.{u} (ringCatSheafOf R) where
  obj F := moduleSheafHomFunctor F.unop
  map f := moduleSheafHomPrecomp f.unop
  map_id F := by
    ext G : 2
    apply SheafOfModules.hom_ext
    ext U σ
    change Hom.over (𝟙 F.unop) U.unop ≫ σ ≫ Hom.over (𝟙 G) U.unop = σ
    obtain ⟨τ, rfl⟩ : ∃ τ : F.unop.over U.unop ⟶ G.over U.unop, τ = σ := ⟨σ, rfl⟩
    simp
  map_comp {F F' F''} f g := by
    ext G : 2
    apply SheafOfModules.hom_ext
    ext U σ
    change Hom.over (g.unop ≫ f.unop) U.unop ≫ σ ≫ Hom.over (𝟙 G) U.unop =
      Hom.over g.unop U.unop ≫
        (Hom.over f.unop U.unop ≫ σ ≫ Hom.over (𝟙 G) U.unop) ≫
          Hom.over (𝟙 G) U.unop
    obtain ⟨τ, rfl⟩ : ∃ τ : F.unop.over U.unop ⟶ G.over U.unop, τ = σ := ⟨σ, rfl⟩
    simp

lemma moduleSheafHomPrecomp_zero {F' F : SheafOfModules.{u} (ringCatSheafOf R)} :
    moduleSheafHomPrecomp (0 : F' ⟶ F) = 0 := by
  ext G : 2
  apply SheafOfModules.hom_ext
  ext U σ
  obtain ⟨τ, rfl⟩ : ∃ τ : F.over U.unop ⟶ G.over U.unop, τ = σ := ⟨σ, rfl⟩
  change (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) U.unop).map 0 ≫ τ ≫
    (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) U.unop).map (𝟙 G) = 0
  rw [CategoryTheory.Functor.map_zero, zero_comp]

section Sections

variable {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))} (hS : S.ShortExact)
  (J : SheafOfModules.{u} (ringCatSheafOf R)) (V : (Opens X)ᵒᵖ)

instance (U : Opens X) : (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) U).IsLeftAdjoint :=
  (restrictionAdjunction U).isLeftAdjoint

include hS in
lemma moduleSheafHomPrecomp_g_injective :
    Function.Injective (((moduleSheafHomPrecomp S.g).app J).val.app V) := by
  intro σ τ h
  obtain ⟨σ', rfl⟩ : ∃ σ' : S.X₃.over V.unop ⟶ J.over V.unop, σ' = σ := ⟨σ, rfl⟩
  obtain ⟨τ', rfl⟩ : ∃ τ' : S.X₃.over V.unop ⟶ J.over V.unop, τ' = τ := ⟨τ, rfl⟩
  have := hS.epi_g
  have h' : (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map S.g ≫ σ' ≫
      (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map (𝟙 J) =
      (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map S.g ≫ τ' ≫
      (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map (𝟙 J) := h
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at h'
  exact (cancel_epi _).1 h'

include hS in
lemma moduleSheafHomPrecomp_exact (ψ : (moduleSheafHom S.X₂ J).val.obj V)
    (hψ : ((moduleSheafHomPrecomp S.f).app J).val.app V ψ = 0) :
    ∃ σ, ((moduleSheafHomPrecomp S.g).app J).val.app V σ = ψ := by
  obtain ⟨ψ', rfl⟩ : ∃ ψ' : S.X₂.over V.unop ⟶ J.over V.unop, ψ' = ψ := ⟨ψ, rfl⟩
  have := (restrictionAdjunction (R := R) V.unop).leftAdjoint_preservesColimits
  have hSV := hS.map_of_exact (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop)
  have hψ' : (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map S.f ≫ ψ' = 0 := by
    have h : (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map S.f ≫ ψ' ≫
        (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map (𝟙 J) = 0 := hψ
    simpa using h
  obtain ⟨σ, hσ⟩ : ∃ σ : S.X₃.over V.unop ⟶ J.over V.unop,
      (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map S.g ≫ σ = ψ' :=
    ⟨_, (CokernelCofork.IsColimit.desc' hSV.gIsCokernel ψ' hψ').2⟩
  refine ⟨σ, ?_⟩
  change (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map S.g ≫ σ ≫
    (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map (𝟙 J) = ψ'
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact hσ

include hS in
lemma moduleSheafHomPrecomp_f_surjective [Injective J] :
    Function.Surjective (((moduleSheafHomPrecomp S.f).app J).val.app V) := by
  intro σ
  obtain ⟨σ', rfl⟩ : ∃ σ' : S.X₁.over V.unop ⟶ J.over V.unop, σ' = σ := ⟨σ, rfl⟩
  have := hS.mono_f
  have := injective_over J V.unop
  refine ⟨Injective.factorThru σ'
    ((SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map S.f), ?_⟩
  change (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map S.f ≫ _ ≫
    (SheafOfModules.overFunctor.{u} (ringCatSheafOf R) V.unop).map (𝟙 J) = σ'
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Injective.comp_factorThru]

end Sections

end ModuleSheafHom

/-! ### The contravariant long exact sequence of sheaf `ℰxt` -/

section ContravariantSequence

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

attribute [local instance 2000] Abelian.toPreadditive

/-- The additivity of `ℋom(F, -)`, stated for the preadditive structure underlying the abelian
structure of the category of module sheaves. -/
private theorem moduleSheafHomFunctor_additive' (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    @Functor.Additive _ _ _ _ (@Abelian.toPreadditive _ _ sheafOfModules_abelian)
      (@Abelian.toPreadditive _ _ sheafOfModules_abelian) (moduleSheafHomFunctor F) :=
  moduleSheafHomFunctor_additive F

attribute [local instance 3000] moduleSheafHomFunctor_additive'

/-- Injective resolutions of module sheaves, as a single constant (see
`Hartshorne.RingedSpace.SheafExtLongExact`). -/
private theorem sheafOfModules_hasInjectiveResolutions :
    HasInjectiveResolutions (SheafOfModules.{u} (ringCatSheafOf R)) :=
  inferInstance

attribute [local instance 3000] sheafOfModules_hasInjectiveResolutions

instance (F : (SheafOfModules.{u} (ringCatSheafOf R))ᵒᵖ) :
    ((moduleSheafHomBifunctor R).obj F).Additive :=
  moduleSheafHomFunctor_additive' F.unop

instance (F : (SheafOfModules.{u} (ringCatSheafOf R))ᵒᵖ) :
    PreservesFiniteLimits ((moduleSheafHomBifunctor R).obj F) :=
  inferInstanceAs (PreservesFiniteLimits (moduleSheafHomFunctor F.unop))

instance : (moduleSheafHomBifunctor R).PreservesZeroMorphisms where
  map_zero F F' := by
    change moduleSheafHomPrecomp (0 : F ⟶ F').unop = 0
    rw [unop_zero]
    exact moduleSheafHomPrecomp_zero

/-- **`ℋom(-, J)` is exact for an injective `J`** (Hartshorne III.6, proof of Proposition 6.4):
for a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of `𝒪_X`-modules and an injective `𝒪_X`-module
`J`, the sequence `0 ⟶ ℋom(F'', J) ⟶ ℋom(F, J) ⟶ ℋom(F', J) ⟶ 0` is short exact. On sections over
`U` it is the sequence of morphisms into `J|_U`, which is injective by Lemma 6.1. -/
theorem moduleSheafHom_shortExact_of_injective (J : SheafOfModules.{u} (ringCatSheafOf R))
    [Injective J] {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))} (hS : S.ShortExact) :
    (ShortComplex.mk (((moduleSheafHomBifunctor R).map S.g.op).app J)
      (((moduleSheafHomBifunctor R).map S.f.op).app J)
      (SheafExtContravariant.map_g_op_app_comp_map_f_op_app _ S J)).ShortExact := by
  have := (SheafOfModules.fullyFaithfulForget (ringCatSheafOf R)).full
  have := (SheafOfModules.fullyFaithfulForget (ringCatSheafOf R)).faithful
  have hmono : Mono ((moduleSheafHomPrecomp S.g).app J) :=
    (SheafOfModules.forget _).mono_of_mono_map
      (PresheafOfModules.mono_of_injective fun V ↦ moduleSheafHomPrecomp_g_injective hS J V)
  have hepi : Epi ((moduleSheafHomPrecomp S.f).app J) :=
    (SheafOfModules.forget _).epi_of_epi_map
      (PresheafOfModules.epi_of_surjective fun V ↦ moduleSheafHomPrecomp_f_surjective hS J V)
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  apply ShortComplex.exact_of_f_is_kernel
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro V
  let G := SheafOfModules.forget (ringCatSheafOf R) ⋙ PresheafOfModules.evaluation _ V
  let Q := ShortComplex.mk (((moduleSheafHomBifunctor R).map S.g.op).app J)
    (((moduleSheafHomBifunctor R).map S.f.op).app J)
    (SheafExtContravariant.map_g_op_app_comp_map_f_op_app _ S J)
  have hV : (Q.map G).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro ψ hψ
    exact moduleSheafHomPrecomp_exact hS J V ψ hψ
  have : Mono (Q.map G).f :=
    (ModuleCat.mono_iff_injective _).2 (moduleSheafHomPrecomp_g_injective hS J V)
  exact (KernelFork.isLimitMapConeEquiv (KernelFork.ofι Q.f Q.zero) G).symm hV.fIsKernel

private theorem rightDerived_eq_sheafExt' (F : SheafOfModules.{u} (ringCatSheafOf R)) (n : ℕ) :
    ((moduleSheafHomBifunctor R).obj (op F)).rightDerived n = sheafExt F n :=
  rfl

/-- The map `ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F', G)` induced by `f : F' ⟶ F`: the morphism between the right
derived functors of `ℋom(F, -)` and `ℋom(F', -)` induced by precomposition with `f`. -/
noncomputable def sheafExtPrecomp {F' F : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F)
    (G : SheafOfModules.{u} (ringCatSheafOf R)) (n : ℕ) :
    (sheafExt F n).obj G ⟶ (sheafExt F' n).obj G :=
  SheafExtContravariant.extMap (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' f G n

variable {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))} (hS : S.ShortExact)
  (G : SheafOfModules.{u} (ringCatSheafOf R))

/-- The connecting morphism `ℰxtⁿ(F', G) ⟶ ℰxtⁿ⁺¹(F'', G)` of the contravariant long exact sequence
attached to a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` (Hartshorne III.6, Proposition 6.4):
for the chosen injective resolution `G ⟶ I^•`, the connecting morphism of the cohomology sequence
of the short exact sequence of complexes `0 ⟶ ℋom(F'', I^•) ⟶ ℋom(F, I^•) ⟶ ℋom(F', I^•) ⟶ 0`. -/
noncomputable def sheafExtContraδ (n : ℕ) :
    (sheafExt S.X₁ n).obj G ⟶ (sheafExt S.X₃ (n + 1)).obj G :=
  SheafExtContravariant.δ (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G n

/-- The first connecting morphism `ℋom(F', G) ⟶ ℰxt¹(F'', G)` of the contravariant long exact
sequence: the canonical map `ℋom(F', G) ⟶ ℰxt⁰(F', G)` followed by the connecting morphism
`ℰxt⁰(F', G) ⟶ ℰxt¹(F'', G)`. -/
noncomputable def sheafHomContraδ : (moduleSheafHomFunctor S.X₁).obj G ⟶ (sheafExt S.X₃ 1).obj G :=
  SheafExtContravariant.homδ (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G

/-- The composite `ℋom(F'', G) ⟶ ℋom(F, G) ⟶ ℋom(F', G)` vanishes. -/
lemma moduleSheafHomPrecomp_g_comp_f :
    (moduleSheafHomPrecomp S.g).app G ≫ (moduleSheafHomPrecomp S.f).app G = 0 :=
  SheafExtContravariant.map_g_op_app_comp_map_f_op_app (moduleSheafHomBifunctor R) S G

/-- The composite `ℋom(F, G) ⟶ ℋom(F', G) ⟶ ℰxt¹(F'', G)` vanishes. -/
lemma moduleSheafHomPrecomp_f_comp_sheafHomContraδ :
    (moduleSheafHomPrecomp S.f).app G ≫ sheafHomContraδ hS G = 0 :=
  SheafExtContravariant.map_f_op_app_comp_homδ (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G

/-- The composite `ℋom(F', G) ⟶ ℰxt¹(F'', G) ⟶ ℰxt¹(F, G)` vanishes. -/
lemma sheafHomContraδ_comp_sheafExtPrecomp :
    sheafHomContraδ hS G ≫ sheafExtPrecomp S.g G 1 = 0 :=
  SheafExtContravariant.homδ_comp_extMap_g (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G

/-- The composite `ℰxtⁿ(F'', G) ⟶ ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F', G)` vanishes. -/
lemma sheafExtPrecomp_g_comp_f (n : ℕ) :
    sheafExtPrecomp S.g G n ≫ sheafExtPrecomp S.f G n = 0 :=
  SheafExtContravariant.extMap_g_comp_extMap_f (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' S G n

/-- The composite `ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F', G) ⟶ ℰxtⁿ⁺¹(F'', G)` vanishes. -/
lemma sheafExtPrecomp_f_comp_sheafExtContraδ (n : ℕ) :
    sheafExtPrecomp S.f G n ≫ sheafExtContraδ hS G n = 0 :=
  SheafExtContravariant.extMap_f_comp_δ (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G n

/-- The composite `ℰxtⁿ(F', G) ⟶ ℰxtⁿ⁺¹(F'', G) ⟶ ℰxtⁿ⁺¹(F, G)` vanishes. -/
lemma sheafExtContraδ_comp_sheafExtPrecomp (n : ℕ) :
    sheafExtContraδ hS G n ≫ sheafExtPrecomp S.g G (n + 1) = 0 :=
  SheafExtContravariant.δ_comp_extMap_g (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G n

include hS in
/-- **The contravariant sequence starts with `0`** (Hartshorne III.6, Proposition 6.4): for a short
exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0`, the map `ℋom(F'', G) ⟶ ℋom(F, G)` is a monomorphism. -/
theorem sheafHom_contra_mono : Mono ((moduleSheafHomPrecomp S.g).app G) :=
  SheafExtContravariant.hom_mono (moduleSheafHomBifunctor R)
    moduleSheafHom_shortExact_of_injective hS G

include hS in
/-- Exactness of `ℋom(F'', G) ⟶ ℋom(F, G) ⟶ ℋom(F', G)` (Hartshorne III.6, Proposition 6.4). -/
theorem sheafHom_contra_exact₂ :
    (ShortComplex.mk ((moduleSheafHomPrecomp S.g).app G) ((moduleSheafHomPrecomp S.f).app G)
      (moduleSheafHomPrecomp_g_comp_f G)).Exact :=
  SheafExtContravariant.hom_exact₂ (moduleSheafHomBifunctor R)
    moduleSheafHom_shortExact_of_injective hS G _

/-- Exactness of `ℋom(F, G) ⟶ ℋom(F', G) ⟶ ℰxt¹(F'', G)` (Hartshorne III.6, Proposition 6.4). -/
theorem sheafHom_contra_exact₃ :
    (ShortComplex.mk ((moduleSheafHomPrecomp S.f).app G) (sheafHomContraδ hS G)
      (moduleSheafHomPrecomp_f_comp_sheafHomContraδ hS G)).Exact :=
  SheafExtContravariant.hom_exact₃ (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G _

/-- Exactness of `ℋom(F', G) ⟶ ℰxt¹(F'', G) ⟶ ℰxt¹(F, G)` (Hartshorne III.6, Proposition 6.4). -/
theorem sheafHom_contra_exact₁ :
    (ShortComplex.mk (sheafHomContraδ hS G) (sheafExtPrecomp S.g G 1)
      (sheafHomContraδ_comp_sheafExtPrecomp hS G)).Exact :=
  SheafExtContravariant.hom_exact₁ (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G _

include hS in
/-- Exactness of `ℰxtⁿ(F'', G) ⟶ ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F', G)` (Hartshorne III.6, Proposition 6.4). -/
theorem sheafExt_contra_exact₂ (n : ℕ) :
    (ShortComplex.mk (sheafExtPrecomp S.g G n) (sheafExtPrecomp S.f G n)
      (sheafExtPrecomp_g_comp_f G n)).Exact :=
  SheafExtContravariant.exact₂ (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G n _

/-- Exactness of `ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F', G) ⟶ ℰxtⁿ⁺¹(F'', G)` (Hartshorne III.6,
Proposition 6.4). -/
theorem sheafExt_contra_exact₃ (n : ℕ) :
    (ShortComplex.mk (sheafExtPrecomp S.f G n) (sheafExtContraδ hS G n)
      (sheafExtPrecomp_f_comp_sheafExtContraδ hS G n)).Exact :=
  SheafExtContravariant.exact₃ (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G n _

/-- Exactness of `ℰxtⁿ(F', G) ⟶ ℰxtⁿ⁺¹(F'', G) ⟶ ℰxtⁿ⁺¹(F, G)` (Hartshorne III.6,
Proposition 6.4). -/
theorem sheafExt_contra_exact₁ (n : ℕ) :
    (ShortComplex.mk (sheafExtContraδ hS G n) (sheafExtPrecomp S.g G (n + 1))
      (sheafExtContraδ_comp_sheafExtPrecomp hS G n)).Exact :=
  SheafExtContravariant.exact₁ (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective hS G n _

/-- **Naturality of the first connecting morphism** `ℋom(F', G) ⟶ ℰxt¹(F'', G)` in morphisms of
short exact sequences (Hartshorne III.6, Proposition 6.4). -/
theorem sheafHomContraδ_naturality {S₁ S₂ : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) :
    sheafHomContraδ hS₂ G ≫ sheafExtPrecomp φ.τ₃ G 1 =
      (moduleSheafHomPrecomp φ.τ₁).app G ≫ sheafHomContraδ hS₁ G :=
  SheafExtContravariant.homδ_naturality (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective φ hS₁ hS₂ G

/-- **Naturality of the connecting morphisms** `ℰxtⁿ(F', G) ⟶ ℰxtⁿ⁺¹(F'', G)` in morphisms of short
exact sequences (Hartshorne III.6, Proposition 6.4). -/
theorem sheafExtContraδ_naturality {S₁ S₂ : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n : ℕ) :
    sheafExtContraδ hS₂ G n ≫ sheafExtPrecomp φ.τ₃ G (n + 1) =
      sheafExtPrecomp φ.τ₁ G n ≫ sheafExtContraδ hS₁ G n :=
  SheafExtContravariant.δ_naturality (moduleSheafHomBifunctor R) sheafExt
    rightDerived_eq_sheafExt' moduleSheafHom_shortExact_of_injective φ hS₁ hS₂ G n

end ContravariantSequence

end Ringed

end Hartshorne
