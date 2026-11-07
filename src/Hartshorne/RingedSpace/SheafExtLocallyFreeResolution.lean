/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtContravariant
import Hartshorne.RingedSpace.SheafExtFiniteLocallyFree
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Locally free resolutions compute `ℰxt`

Hartshorne, *Algebraic Geometry*, III.6, Proposition 6.5 (p. 234).

Let `(X, 𝒪_X)` be a ringed space and `L_• ⟶ F ⟶ 0` a resolution of an `𝒪_X`-module `F` by
locally free `𝒪_X`-modules of finite rank, possibly unbounded to the left: a chain complex `L`
indexed by `ℕ` with a quasi-isomorphism `L ⟶ F[0]`. For every `𝒪_X`-module `G` there are
isomorphisms `ℰxtⁱ(F, G) ≅ hⁱ(ℋom(L_•, G))`, natural in `G`
(`Hartshorne.Ringed.sheafExtIsoHomologyOfLocallyFreeResolution`); here `ℋom(L_•, G)` is the cochain
complex `Hartshorne.Ringed.moduleSheafHomComplex L`, functorial in `G`.

## Proof

Dimension shifting in the first variable. Write `K = ker(L₀ ⟶ F)`, so that `0 ⟶ K ⟶ L₀ ⟶ F ⟶ 0`
is exact and the truncated complex `L_{•+1} ⟶ K` is again a resolution. Since `L₀` is finite
locally free, `ℰxtⁱ(L₀, G) = 0` for `i > 0`
(`Hartshorne.Ringed.isZero_sheafExt_of_isFiniteLocallyFree`), so the contravariant long exact
sequence (Proposition 6.4) gives

* `ℰxt⁰(F, G) = ℋom(F, G) = ker(ℋom(L₀, G) ⟶ ℋom(L₁, G))` by left exactness of `ℋom(-, G)`;
* `ℰxt¹(F, G) = coker(ℋom(L₀, G) ⟶ ℋom(K, G))`, and `ℋom(K, G) = ker(ℋom(L₁, G) ⟶ ℋom(L₂, G))`;
* `ℰxtⁱ⁺¹(F, G) ≅ ℰxtⁱ(K, G)` for `i ≥ 1`, through the connecting morphism.

Induction on the degree, over all resolutions at once, gives the result. Naturality in `G` uses
that the connecting morphisms of the contravariant sequence are natural in `G`
(`Hartshorne.Ringed.LocallyFreeResolutionExt.δ_naturality_right`).

The homological algebra is done for an abstract bifunctor `H : Cᵒᵖ ⥤ C ⥤ C` and functors `E F n`
equal to the right derived functors of `H(F, -)`, in the setting of
`Hartshorne.RingedSpace.SheafExtContravariant`, and then specialized to `ℋom` and `ℰxt`.
-/

universe u v' u'

open CategoryTheory Limits Opposite

namespace Hartshorne

namespace Ringed

namespace LocallyFreeResolutionExt

/-! ### Natural isomorphisms between kernels and between cokernels -/

section Helpers

variable {D : Type*} [Category D] {C : Type u'} [Category.{v'} C] [Abelian C]

/-- The natural transformation between two families of kernels of the same morphisms. -/
@[simps]
noncomputable def natTransOfKernels {T₁ T₂ A : D ⥤ C} (ι₁ : T₁ ⟶ A) (ι₂ : T₂ ⟶ A) {B : D → C}
    (g : ∀ G, A.obj G ⟶ B G) (w₁ : ∀ G, ι₁.app G ≫ g G = 0) (w₂ : ∀ G, ι₂.app G ≫ g G = 0)
    (h₂ : ∀ G, (ShortComplex.mk _ _ (w₂ G)).Exact) [∀ G, Mono (ι₂.app G)] : T₁ ⟶ T₂ where
  app G := (h₂ G).lift (ι₁.app G) (w₁ G)
  naturality G G' f := by
    apply (cancel_mono (ι₂.app G')).1
    rw [Category.assoc, Category.assoc, ι₂.naturality, ← Category.assoc _ (ι₂.app G)]
    erw [(h₂ G').lift_f, (h₂ G).lift_f]
    exact ι₁.naturality f

/-- Two families of kernels of the same morphisms, given by natural transformations into the same
functor, are naturally isomorphic. -/
noncomputable def natIsoOfKernels {T₁ T₂ A : D ⥤ C} (ι₁ : T₁ ⟶ A) (ι₂ : T₂ ⟶ A) {B : D → C}
    (g : ∀ G, A.obj G ⟶ B G) (w₁ : ∀ G, ι₁.app G ≫ g G = 0) (w₂ : ∀ G, ι₂.app G ≫ g G = 0)
    (h₁ : ∀ G, (ShortComplex.mk _ _ (w₁ G)).Exact) (h₂ : ∀ G, (ShortComplex.mk _ _ (w₂ G)).Exact)
    [∀ G, Mono (ι₁.app G)] [∀ G, Mono (ι₂.app G)] : T₁ ≅ T₂ where
  hom := natTransOfKernels ι₁ ι₂ g w₁ w₂ h₂
  inv := natTransOfKernels ι₂ ι₁ g w₂ w₁ h₁
  hom_inv_id := by
    ext G
    apply (cancel_mono (ι₁.app G)).1
    rw [NatTrans.comp_app, Category.assoc, NatTrans.id_app, Category.id_comp]
    erw [(h₁ G).lift_f, (h₂ G).lift_f]
  inv_hom_id := by
    ext G
    apply (cancel_mono (ι₂.app G)).1
    rw [NatTrans.comp_app, Category.assoc, NatTrans.id_app, Category.id_comp]
    erw [(h₂ G).lift_f, (h₁ G).lift_f]

lemma natIsoOfKernels_hom_app_comp {T₁ T₂ A : D ⥤ C} (ι₁ : T₁ ⟶ A) (ι₂ : T₂ ⟶ A) {B : D → C}
    (g : ∀ G, A.obj G ⟶ B G) (w₁ : ∀ G, ι₁.app G ≫ g G = 0) (w₂ : ∀ G, ι₂.app G ≫ g G = 0)
    (h₁ : ∀ G, (ShortComplex.mk _ _ (w₁ G)).Exact) (h₂ : ∀ G, (ShortComplex.mk _ _ (w₂ G)).Exact)
    [∀ G, Mono (ι₁.app G)] [∀ G, Mono (ι₂.app G)] (G : D) :
    (natIsoOfKernels ι₁ ι₂ g w₁ w₂ h₁ h₂).hom.app G ≫ ι₂.app G = ι₁.app G :=
  (h₂ G).lift_f _ _

/-- The natural transformation between two families of cokernels of the same morphisms. -/
@[simps]
noncomputable def natTransOfCokernels {T₁ T₂ B : D ⥤ C} (p₁ : B ⟶ T₁) (p₂ : B ⟶ T₂) {A : D → C}
    (f : ∀ G, A G ⟶ B.obj G) (w₁ : ∀ G, f G ≫ p₁.app G = 0) (w₂ : ∀ G, f G ≫ p₂.app G = 0)
    (h₁ : ∀ G, (ShortComplex.mk _ _ (w₁ G)).Exact) [∀ G, Epi (p₁.app G)] : T₁ ⟶ T₂ where
  app G := (h₁ G).desc (p₂.app G) (w₂ G)
  naturality G G' φ := by
    apply (cancel_epi (p₁.app G)).1
    rw [← Category.assoc, ← p₁.naturality, Category.assoc]
    erw [(h₁ G').g_desc, ← Category.assoc, (h₁ G).g_desc]
    exact p₂.naturality φ

/-- Two families of cokernels of the same morphisms, given by natural transformations out of the
same functor, are naturally isomorphic. -/
noncomputable def natIsoOfCokernels {T₁ T₂ B : D ⥤ C} (p₁ : B ⟶ T₁) (p₂ : B ⟶ T₂) {A : D → C}
    (f : ∀ G, A G ⟶ B.obj G) (w₁ : ∀ G, f G ≫ p₁.app G = 0) (w₂ : ∀ G, f G ≫ p₂.app G = 0)
    (h₁ : ∀ G, (ShortComplex.mk _ _ (w₁ G)).Exact) (h₂ : ∀ G, (ShortComplex.mk _ _ (w₂ G)).Exact)
    [∀ G, Epi (p₁.app G)] [∀ G, Epi (p₂.app G)] : T₁ ≅ T₂ where
  hom := natTransOfCokernels p₁ p₂ f w₁ w₂ h₁
  inv := natTransOfCokernels p₂ p₁ f w₂ w₁ h₂
  hom_inv_id := by
    ext G
    apply (cancel_epi (p₁.app G)).1
    rw [NatTrans.comp_app, NatTrans.id_app, Category.comp_id, ← Category.assoc]
    erw [(h₁ G).g_desc, (h₂ G).g_desc]
  inv_hom_id := by
    ext G
    apply (cancel_epi (p₂.app G)).1
    rw [NatTrans.comp_app, NatTrans.id_app, Category.comp_id, ← Category.assoc]
    erw [(h₂ G).g_desc, (h₁ G).g_desc]

lemma app_comp_natIsoOfCokernels_hom {T₁ T₂ B : D ⥤ C} (p₁ : B ⟶ T₁) (p₂ : B ⟶ T₂) {A : D → C}
    (f : ∀ G, A G ⟶ B.obj G) (w₁ : ∀ G, f G ≫ p₁.app G = 0) (w₂ : ∀ G, f G ≫ p₂.app G = 0)
    (h₁ : ∀ G, (ShortComplex.mk _ _ (w₁ G)).Exact) (h₂ : ∀ G, (ShortComplex.mk _ _ (w₂ G)).Exact)
    [∀ G, Epi (p₁.app G)] [∀ G, Epi (p₂.app G)] (G : D) :
    p₁.app G ≫ (natIsoOfCokernels p₁ p₂ f w₁ w₂ h₁ h₂).hom.app G = p₂.app G :=
  (h₁ G).g_desc _ _

end Helpers

/-! ### Resolutions -/

section Resolutions

variable {C : Type u'} [Category.{v'} C] [Abelian C]

/-- A resolution `⋯ ⟶ L₁ ⟶ L₀ ⟶ F ⟶ 0` of an object `F`, possibly unbounded: a chain complex
`L` indexed by `ℕ` with an augmentation `ε : L₀ ⟶ F` such that the augmented complex is exact. -/
structure Resolution (F : C) where
  /-- The complex `L_•`. -/
  L : ChainComplex C ℕ
  /-- The augmentation `L₀ ⟶ F`. -/
  ε : L.X 0 ⟶ F
  /-- The composite `L₁ ⟶ L₀ ⟶ F` vanishes. -/
  w : L.d 1 0 ≫ ε = 0
  /-- The augmentation is an epimorphism. -/
  epi_ε : Epi ε
  /-- Exactness at `L₀`. -/
  exact₀ : (ShortComplex.mk _ _ w).Exact
  /-- Exactness at `L_{n+1}`. -/
  exactAt : ∀ n, L.ExactAt (n + 1)

namespace Resolution

variable {F : C} (P : Resolution F)

/-- The short exact sequence `0 ⟶ K ⟶ L₀ ⟶ F ⟶ 0`, where `K = ker(L₀ ⟶ F)`. -/
noncomputable abbrev ses : ShortComplex C :=
  ShortComplex.mk (kernel.ι P.ε) P.ε (kernel.condition _)

lemma ses_shortExact : P.ses.ShortExact := by
  have := P.epi_ε
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    inferInstance this

/-- The map `L₁ ⟶ K = ker(L₀ ⟶ F)` induced by the differential. -/
noncomputable def lift : P.L.X 1 ⟶ kernel P.ε := kernel.lift P.ε (P.L.d 1 0) P.w

@[reassoc (attr := simp)]
lemma lift_ι : P.lift ≫ kernel.ι P.ε = P.L.d 1 0 := kernel.lift_ι _ _ _

lemma epi_lift : Epi P.lift := (ShortComplex.exact_iff_epi_kernel_lift _).1 P.exact₀

lemma truncate_w : ((ChainComplex.truncate).obj P.L).d 1 0 ≫ P.lift = 0 := by
  change P.L.d 2 1 ≫ P.lift = 0
  rw [← cancel_mono (kernel.ι P.ε), Category.assoc, lift_ι, zero_comp]
  exact P.L.d_comp_d 2 1 0

/-- The truncated resolution `L_{•+1} ⟶ K ⟶ 0` of `K = ker(L₀ ⟶ F)`. -/
noncomputable def truncate : Resolution (kernel P.ε) where
  L := (ChainComplex.truncate).obj P.L
  ε := P.lift
  w := P.truncate_w
  epi_ε := P.epi_lift
  exact₀ := by
    have h := (HomologicalComplex.exactAt_iff' P.L 2 1 0 (by simp) (by simp)).1 (P.exactAt 0)
    let φ : ShortComplex.mk _ _ P.truncate_w ⟶ P.L.sc' 2 1 0 :=
      { τ₁ := 𝟙 (P.L.X 2)
        τ₂ := 𝟙 (P.L.X 1)
        τ₃ := kernel.ι P.ε
        comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
        comm₂₃ := (Category.id_comp _).trans P.lift_ι.symm }
    have : Epi φ.τ₁ := (inferInstance : Epi (𝟙 (P.L.X 2)))
    have : IsIso φ.τ₂ := (inferInstance : IsIso (𝟙 (P.L.X 1)))
    have : Mono φ.τ₃ := (inferInstance : Mono (kernel.ι P.ε))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h
  exactAt n := (HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)).2
    ((HomologicalComplex.exactAt_iff' P.L (n + 3) (n + 2) (n + 1) (by simp) (by simp)).1
      (P.exactAt (n + 1)))

@[simp]
lemma truncate_L : P.truncate.L = (ChainComplex.truncate).obj P.L := rfl

@[simp]
lemma truncate_ε : P.truncate.ε = P.lift := rfl

/-- A quasi-isomorphism `L ⟶ F[0]` from a chain complex indexed by `ℕ` is a resolution of `F`. -/
noncomputable def ofQuasiIso (L : ChainComplex C ℕ) (π : L ⟶ (ChainComplex.single₀ C).obj F)
    [QuasiIso π] : Resolution F :=
  have h := (ShortComplex.quasiIso_iff_of_zeros'
    ((HomologicalComplex.shortComplexFunctor' C _ 1 0 0).map π) (by simp; rfl)
      (by simp; rfl) (by simp; rfl)).1 ((ChainComplex.quasiIsoAt₀_iff π).1 inferInstance)
  { L := L
    ε := π.f 0
    w := by
      have h' := π.comm 1 0
      rw [HomologicalComplex.single_obj_d, comp_zero] at h'
      exact h'.symm
    epi_ε := h.2
    exact₀ := h.1
    exactAt := fun n => by
      rw [← quasiIsoAt_iff_exactAt' π (n + 1) (ChainComplex.exactAt_succ_single_obj _ _)]
      infer_instance }

end Resolution

end Resolutions

/-! ### The abstract dimension shifting -/

section Abstract

variable {C : Type u'} [Category.{v'} C] [Abelian C] [HasInjectiveResolutions C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.PreservesZeroMorphisms] [∀ F, (H.obj F).Additive]
  (E : C → ℕ → C ⥤ C) (hE : ∀ F n, (H.obj (op F)).rightDerived n = E F n)

open SheafExtContravariant

/-- The cochain complex `H(L_•, G)` of a chain complex `L`, functorial in `G`. -/
noncomputable def homComplex (L : ChainComplex C ℕ) : C ⥤ CochainComplex C ℕ where
  obj G := CochainComplex.of (fun p => (H.obj (op (L.X p))).obj G)
    (fun p => (H.map (L.d (p + 1) p).op).app G)
    (fun p => by rw [map_op_app_comp_map_op_app, L.d_comp_d, map_op_app_zero])
  map g := CochainComplex.ofHom (fun p => (H.obj (op (L.X p))).map g)
    (fun p => by
      simp only [CochainComplex.of_d]
      exact (H.map (L.d (p + 1) p).op).naturality g)
  map_id G := by ext p; exact (H.obj (op (L.X p))).map_id G
  map_comp f g := by ext p; exact (H.obj (op (L.X p))).map_comp f g

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] in
lemma homComplex_d (L : ChainComplex C ℕ) (G : C) (p : ℕ) :
    ((homComplex H L).obj G).d p (p + 1) = (H.map (L.d (p + 1) p).op).app G := by
  dsimp only [homComplex]
  rw [CochainComplex.of_d]

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] in
@[simp]
lemma homComplex_map_f (L : ChainComplex C ℕ) {G G' : C} (g : G ⟶ G') (p : ℕ) :
    ((homComplex H L).map g).f p = (H.obj (op (L.X p))).map g := rfl

/-! #### Naturality of the connecting morphisms in the second variable -/

omit [H.PreservesZeroMorphisms] in
private lemma isoE_naturality_aux (F : C) (n : ℕ) (E' : C ⥤ C)
    (h : (H.obj (op F)).rightDerived n = E') {G G' : C} (g : G ⟶ G')
    (φ : (injectiveResolution G).cocomplex ⟶ (injectiveResolution G').cocomplex)
    (comm : (injectiveResolution G).ι.f 0 ≫ φ.f 0 = g ≫ (injectiveResolution G').ι.f 0) :
    E'.map g ≫ (eqToIso (Functor.congr_obj h.symm G') ≪≫
        RightDerivedLES.isoH (H.obj (op F)) (injectiveResolution G') n).hom =
      (eqToIso (Functor.congr_obj h.symm G) ≪≫
        RightDerivedLES.isoH (H.obj (op F)) (injectiveResolution G) n).hom ≫
        HomologicalComplex.homologyMap (((H.obj (op F)).mapHomologicalComplex _).map φ) n := by
  subst h
  simpa using RightDerivedLES.map_comp_isoH_hom (H.obj (op F)) g _ _ φ comm n

omit [H.PreservesZeroMorphisms] in
@[reassoc]
lemma isoE_hom_naturality (F : C) {G G' : C} (g : G ⟶ G') (n : ℕ) :
    (E F n).map g ≫ (isoE H E hE F G' n).hom =
      (isoE H E hE F G n).hom ≫ HomologicalComplex.homologyMap
        (((H.obj (op F)).mapHomologicalComplex _).map
          (InjectiveResolution.desc g (injectiveResolution G') (injectiveResolution G))) n :=
  isoE_naturality_aux H F n (E F n) (hE F n) g _ (InjectiveResolution.desc_commutes_zero _ _ _)

omit [H.PreservesZeroMorphisms] in
lemma isoE_inv_naturality (F : C) {G G' : C} (g : G ⟶ G') (n : ℕ) :
    (isoE H E hE F G n).inv ≫ (E F n).map g =
      HomologicalComplex.homologyMap (((H.obj (op F)).mapHomologicalComplex _).map
          (InjectiveResolution.desc g (injectiveResolution G') (injectiveResolution G))) n ≫
        (isoE H E hE F G' n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← isoE_hom_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The morphism of short exact sequences of complexes `H(S, I_G^•) ⟶ H(S, I_{G'}^•)` induced by
`g : G ⟶ G'`. -/
noncomputable def Tdesc (S : ShortComplex C) {G G' : C} (g : G ⟶ G') : T H S G ⟶ T H S G' where
  τ₁ := ((H.obj (op S.X₃)).mapHomologicalComplex _).map
    (InjectiveResolution.desc g (injectiveResolution G') (injectiveResolution G))
  τ₂ := ((H.obj (op S.X₂)).mapHomologicalComplex _).map
    (InjectiveResolution.desc g (injectiveResolution G') (injectiveResolution G))
  τ₃ := ((H.obj (op S.X₁)).mapHomologicalComplex _).map
    (InjectiveResolution.desc g (injectiveResolution G') (injectiveResolution G))
  comm₁₂ := NatTrans.mapHomologicalComplex_naturality _ _
  comm₂₃ := NatTrans.mapHomologicalComplex_naturality _ _

variable (hH : ∀ (J : C) [Injective J] {S : ShortComplex C} (_ : S.ShortExact),
  (ShortComplex.mk ((H.map S.g.op).app J) ((H.map S.f.op).app J)
    (map_g_op_app_comp_map_f_op_app H S J)).ShortExact)

/-- **Naturality of the contravariant connecting morphisms in the second variable.** -/
lemma δ_naturality_right {S : ShortComplex C} (hS : S.ShortExact) {G G' : C} (g : G ⟶ G')
    (n : ℕ) :
    δ H E hE hH hS G n ≫ (E S.X₃ (n + 1)).map g = (E S.X₁ n).map g ≫ δ H E hE hH hS G' n := by
  have h := HomologicalComplex.HomologySequence.δ_naturality (Tdesc H S g)
    (T_shortExact H hH hS G) (T_shortExact H hH hS G') n (n + 1) (RightDerivedLES.upRel n)
  simp only [δ, Category.assoc]
  rw [isoE_inv_naturality, isoE_hom_naturality_assoc]
  change _ ≫ _ ≫ HomologicalComplex.homologyMap (Tdesc H S g).τ₁ (n + 1) ≫ _ =
    _ ≫ HomologicalComplex.homologyMap (Tdesc H S g).τ₃ n ≫ _
  rw [reassoc_of% h]

lemma homδ_naturality_right {S : ShortComplex C} (hS : S.ShortExact) {G G' : C} (g : G ⟶ G') :
    homδ H E hE hH hS G ≫ (E S.X₃ 1).map g =
      (H.obj (op S.X₁)).map g ≫ homδ H E hE hH hS G' := by
  rw [homδ, homδ, Category.assoc, δ_naturality_right, ← Category.assoc, ← Category.assoc,
    (η H E hE S.X₁).naturality]

/-- The connecting morphisms `E S.X₁ n ⟶ E S.X₃ (n + 1)` as a natural transformation. -/
@[simps]
noncomputable def δNat {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    E S.X₁ n ⟶ E S.X₃ (n + 1) where
  app G := δ H E hE hH hS G n
  naturality _ _ g := (δ_naturality_right H E hE hH hS g n).symm

/-- The connecting morphism `H(S.X₁, -) ⟶ E S.X₃ 1` as a natural transformation. -/
@[simps]
noncomputable def homδNat {S : ShortComplex C} (hS : S.ShortExact) :
    H.obj (op S.X₁) ⟶ E S.X₃ 1 where
  app G := homδ H E hE hH hS G
  naturality _ _ g := (homδ_naturality_right H E hE hH hS g).symm

/-- If the middle term of a short exact sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` has vanishing
`E`'s in degrees `n + 1` and `n + 2`, the connecting morphism is an isomorphism
`E S.X₁ (n + 1) ≅ E S.X₃ (n + 2)`. -/
noncomputable def δIso {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (h₁ : ∀ G, IsZero ((E S.X₂ (n + 1)).obj G)) (h₂ : ∀ G, IsZero ((E S.X₂ (n + 2)).obj G)) :
    E S.X₁ (n + 1) ≅ E S.X₃ (n + 2) :=
  haveI : ∀ G, IsIso ((δNat H E hE hH hS (n + 1)).app G) := fun G => by
    have hm : Mono (δ H E hE hH hS G (n + 1)) :=
      (exact₃ H E hE hH hS G (n + 1) (extMap_f_comp_δ H E hE hH hS G (n + 1))).mono_g
        ((h₁ G).eq_of_src _ _)
    have he : Epi (δ H E hE hH hS G (n + 1)) :=
      (exact₁ H E hE hH hS G (n + 1) (δ_comp_extMap_g H E hE hH hS G (n + 1))).epi_f
        ((h₂ G).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi (δ H E hE hH hS G (n + 1))
  haveI := NatIso.isIso_of_isIso_app (δNat H E hE hH hS (n + 1))
  asIso (δNat H E hE hH hS (n + 1))

omit [HasInjectiveResolutions C] in
lemma exact_of_g_eq {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g g' : X₂ ⟶ X₃} (h : g = g')
    {w : f ≫ g = 0} (hS : (ShortComplex.mk f g' (h ▸ w)).Exact) :
    (ShortComplex.mk f g w).Exact := by
  subst h
  exact hS

variable [∀ F, PreservesFiniteLimits (H.obj F)]

include hH in
lemma Resolution.homMono {F : C} (P : Resolution F) (G : C) : Mono ((H.map P.ε.op).app G) :=
  hom_mono H hH P.ses_shortExact G

include hH in
/-- Left exactness of `H(-, G)` on a resolution: `0 ⟶ H(F, G) ⟶ H(L₀, G) ⟶ H(L₁, G)` is
exact. -/
lemma Resolution.homExact {F : C} (P : Resolution F) (G : C) :
    (ShortComplex.mk ((H.map P.ε.op).app G) ((H.map (P.L.d 1 0).op).app G)
      (by rw [map_op_app_comp_map_op_app, P.w, map_op_app_zero])).Exact := by
  have h₁ := hom_exact₂ H hH P.ses_shortExact G (map_g_op_app_comp_map_f_op_app H _ G)
  have hm : Mono ((H.map P.lift.op).app G) := hom_mono H hH P.truncate.ses_shortExact G
  let φ : ShortComplex.mk _ _ (map_g_op_app_comp_map_f_op_app H P.ses G) ⟶
      ShortComplex.mk ((H.map P.ε.op).app G) ((H.map (P.L.d 1 0).op).app G)
        (by rw [map_op_app_comp_map_op_app, P.w, map_op_app_zero]) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (H.map P.lift.op).app G
      comm₁₂ := by simp
      comm₂₃ := by
        dsimp
        rw [Category.id_comp, map_op_app_comp_map_op_app, Resolution.lift_ι] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 h₁

omit [HasInjectiveResolutions C] in
/-- The inclusion of cycles `K.cycles i ⟶ K.X i`, as a natural transformation. -/
@[simps]
noncomputable def iCyclesNat (i : ℕ) :
    HomologicalComplex.cyclesFunctor C (ComplexShape.up ℕ) i ⟶
      HomologicalComplex.eval C (ComplexShape.up ℕ) i where
  app K := K.iCycles i
  naturality _ _ φ := HomologicalComplex.cyclesMap_i φ i

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] [∀ F, PreservesFiniteLimits (H.obj F)] in
/-- The natural transformation `H(F, -) ⟶ H(L_p, -)` induced by `f : L_p ⟶ F`, viewed as landing
in degree `p` of `H(L_•, -)`. -/
@[simps]
noncomputable def homNat (L : ChainComplex C ℕ) (p : ℕ) {F : C} (f : L.X p ⟶ F) :
    H.obj (op F) ⟶ homComplex H L ⋙ HomologicalComplex.eval C (ComplexShape.up ℕ) p where
  app G := (H.map f.op).app G
  naturality _ _ g := (H.map f.op).naturality g

omit [HasInjectiveResolutions C] in
/-- The natural isomorphism `K.cycles 0 ≅ K.homology 0` for cochain complexes. -/
noncomputable def cyclesIsoHomologyZero :
    HomologicalComplex.cyclesFunctor C (ComplexShape.up ℕ) 0 ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) 0 :=
  NatIso.ofComponents (fun K => CochainComplex.isoHomologyπ₀ K)
    (fun φ => (HomologicalComplex.homologyπ_naturality φ 0).symm)

omit [HasInjectiveResolutions C] in
lemma exact_iCycles_d (K : CochainComplex C ℕ) (i : ℕ) :
    (ShortComplex.mk (K.iCycles i) (K.d i (i + 1)) (K.iCycles_d i (i + 1))).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i (i + 1) (by simp))

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] [∀ F, PreservesFiniteLimits (H.obj F)] in
lemma homNat_app_comp_d (L : ChainComplex C ℕ) (p : ℕ) {F : C} (f : L.X p ⟶ F) (G : C) :
    (homNat H L p f).app G ≫ ((homComplex H L).obj G).d p (p + 1) =
      (H.map (L.d (p + 1) p ≫ f).op).app G := by
  rw [homNat_app]
  erw [homComplex_d]
  exact map_op_app_comp_map_op_app H _ _ G

include hH in
lemma exact_homNat_d {F : C} (P : Resolution F) (G : C) :
    (ShortComplex.mk ((homNat H P.L 0 P.ε).app G) (((homComplex H P.L).obj G).d 0 1)
      ((homNat_app_comp_d H P.L 0 P.ε G).trans (by rw [P.w, map_op_app_zero]; rfl))).Exact :=
  exact_of_g_eq (homComplex_d H P.L G 0) (P.homExact H hH G)

/-- Degree zero: `E F 0 ≅ H(F, -) ≅ h⁰(H(L_•, -))`. -/
noncomputable def iso0 {F : C} (P : Resolution F) :
    E F 0 ≅ homComplex H P.L ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) 0 :=
  haveI : ∀ G, Mono ((homNat H P.L 0 P.ε).app G) := fun _ => P.homMono H hH _
  haveI : ∀ G, Mono ((Functor.whiskerLeft (homComplex H P.L) (iCyclesNat 0)).app G) :=
    fun G => (inferInstance : Mono (((homComplex H P.L).obj G).iCycles 0))
  (asIso (η H E hE F)).symm ≪≫
    natIsoOfKernels (homNat H P.L 0 P.ε) (Functor.whiskerLeft (homComplex H P.L) (iCyclesNat 0))
      (fun G => ((homComplex H P.L).obj G).d 0 1) _ (fun _ => HomologicalComplex.iCycles_d _ 0 1)
      (exact_homNat_d H hH P) (fun _ => exact_iCycles_d _ 0) ≪≫
    Functor.isoWhiskerLeft (homComplex H P.L) cyclesIsoHomologyZero

include hH in
lemma exact_homNat_d_one {F : C} (P : Resolution F) (G : C) :
    (ShortComplex.mk ((homNat H P.L 1 P.lift).app G) (((homComplex H P.L).obj G).d 1 2)
      ((homNat_app_comp_d H P.L 1 P.lift G).trans
        (by erw [P.truncate_w]; exact map_op_app_zero H G))).Exact :=
  exact_of_g_eq (homComplex_d H P.L G 1) (P.truncate.homExact H hH G)

/-- `H(K, -) ≅ Z¹(H(L_•, -))` for `K = ker(L₀ ⟶ F)`. -/
noncomputable def cyclesOneIso {F : C} (P : Resolution F) :
    H.obj (op (kernel P.ε)) ≅
      homComplex H P.L ⋙ HomologicalComplex.cyclesFunctor C (ComplexShape.up ℕ) 1 :=
  haveI : ∀ G, Mono ((homNat H P.L 1 P.lift).app G) := fun _ => P.truncate.homMono H hH _
  haveI : ∀ G, Mono ((Functor.whiskerLeft (homComplex H P.L) (iCyclesNat 1)).app G) :=
    fun G => (inferInstance : Mono (((homComplex H P.L).obj G).iCycles 1))
  natIsoOfKernels (homNat H P.L 1 P.lift) (Functor.whiskerLeft (homComplex H P.L) (iCyclesNat 1))
    (fun G => ((homComplex H P.L).obj G).d 1 2) _ (fun _ => HomologicalComplex.iCycles_d _ 1 2)
    (exact_homNat_d_one H hH P) (fun _ => exact_iCycles_d _ 1)

lemma cyclesOneIso_hom_app_iCycles {F : C} (P : Resolution F) (G : C) :
    (cyclesOneIso H hH P).hom.app G ≫ ((homComplex H P.L).obj G).iCycles 1 =
      (H.map P.lift.op).app G := by
  have : ∀ G, Mono ((homNat H P.L 1 P.lift).app G) := fun _ => P.truncate.homMono H hH _
  have : ∀ G, Mono ((Functor.whiskerLeft (homComplex H P.L) (iCyclesNat 1)).app G) :=
    fun G => (inferInstance : Mono (((homComplex H P.L).obj G).iCycles 1))
  exact natIsoOfKernels_hom_app_comp _ _ _ _ _ _ _ G

lemma homNat_ι_comp_cyclesOneIso {F : C} (P : Resolution F) (G : C) :
    (H.map (kernel.ι P.ε).op).app G ≫ (cyclesOneIso H hH P).hom.app G =
      ((homComplex H P.L).obj G).toCycles 0 1 := by
  apply (cancel_mono (((homComplex H P.L).obj G).iCycles 1)).1
  erw [Category.assoc, cyclesOneIso_hom_app_iCycles, HomologicalComplex.toCycles_i]
  refine (map_op_app_comp_map_op_app H _ _ G).trans ?_
  rw [Resolution.lift_ι]
  exact (homComplex_d H P.L G 0).symm

/-- The projection `H(K, -) ≅ Z¹(H(L_•, -)) ⟶ h¹(H(L_•, -))`. -/
noncomputable def toHomologyOne {F : C} (P : Resolution F) :
    H.obj (op (kernel P.ε)) ⟶
      homComplex H P.L ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) 1 :=
  (cyclesOneIso H hH P).hom ≫ Functor.whiskerLeft (homComplex H P.L)
    (HomologicalComplex.natTransHomologyπ C (ComplexShape.up ℕ) 1)

lemma toHomologyOne_app {F : C} (P : Resolution F) (G : C) :
    (toHomologyOne H hH P).app G =
      (cyclesOneIso H hH P).hom.app G ≫ ((homComplex H P.L).obj G).homologyπ 1 := rfl

lemma exact_toHomologyOne {F : C} (P : Resolution F) (G : C) :
    (ShortComplex.mk ((H.map (kernel.ι P.ε).op).app G) ((toHomologyOne H hH P).app G) (by
      rw [toHomologyOne_app]
      erw [reassoc_of% (homNat_ι_comp_cyclesOneIso H hH P G)]
      exact HomologicalComplex.toCycles_comp_homologyπ _ 0 1)).Exact := by
  let S₂ := ShortComplex.mk (((homComplex H P.L).obj G).toCycles 0 1)
    (((homComplex H P.L).obj G).homologyπ 1) (HomologicalComplex.toCycles_comp_homologyπ _ 0 1)
  have hS₂ : S₂.Exact := ShortComplex.exact_of_g_is_cokernel _
    (((homComplex H P.L).obj G).homologyIsCokernel 0 1 (by simp))
  refine (ShortComplex.exact_iff_of_iso (S₂ := S₂) ?_).2 hS₂
  exact ShortComplex.isoMk (Iso.refl _) ((cyclesOneIso H hH P).app G) (Iso.refl _)
    ((Category.id_comp _).trans (homNat_ι_comp_cyclesOneIso H hH P G).symm)
    (Category.comp_id _).symm

/-- Degree one: `E F 1 ≅ coker(H(L₀, -) ⟶ H(K, -)) ≅ h¹(H(L_•, -))`. -/
noncomputable def iso1 {F : C} (P : Resolution F)
    (hacyc : ∀ G, IsZero ((E (P.L.X 0) 1).obj G)) :
    E F 1 ≅ homComplex H P.L ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) 1 :=
  haveI : ∀ G, Epi ((homδNat H E hE hH P.ses_shortExact).app G) := fun G =>
    (hom_exact₁ H E hE hH P.ses_shortExact G
      (homδ_comp_extMap_g H E hE hH P.ses_shortExact G)).epi_f ((hacyc G).eq_of_tgt _ _)
  haveI : ∀ G, Epi ((toHomologyOne H hH P).app G) := fun G =>
    @epi_comp _ _ _ _ _ ((cyclesOneIso H hH P).hom.app G) inferInstance
      (((homComplex H P.L).obj G).homologyπ 1)
      (epi_of_isColimit_cofork (((homComplex H P.L).obj G).homologyIsCokernel 0 1 (by simp)))
  natIsoOfCokernels (homδNat H E hE hH P.ses_shortExact) (toHomologyOne H hH P)
    (fun G => (H.map (kernel.ι P.ε).op).app G)
    (fun G => map_f_op_app_comp_homδ H E hE hH P.ses_shortExact G) _
    (fun G => hom_exact₃ H E hE hH P.ses_shortExact G _) (exact_toHomologyOne H hH P)

omit [HasInjectiveResolutions C] [∀ F, (H.obj F).Additive] [∀ F, PreservesFiniteLimits (H.obj F)] in
/-- The complexes `H(L_{•+1}, G)` and `H(L_•, G)` agree in the relevant degrees. -/
noncomputable def scShiftIso {F : C} (P : Resolution F) (n : ℕ) :
    homComplex H P.truncate.L ⋙ HomologicalComplex.shortComplexFunctor' C _ n (n + 1) (n + 2) ≅
      homComplex H P.L ⋙
        HomologicalComplex.shortComplexFunctor' C _ (n + 1) (n + 2) (n + 3) :=
  NatIso.ofComponents
    (fun G => ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans ((homComplex_d H P.L G (n + 1)).trans
        ((homComplex_d H P.truncate.L G n).symm.trans (Category.comp_id _).symm)))
      ((Category.id_comp _).trans ((homComplex_d H P.L G (n + 2)).trans
        ((homComplex_d H P.truncate.L G (n + 1)).symm.trans (Category.comp_id _).symm))))
    (fun g => by
      ext <;> exact (Category.comp_id _).trans (Category.id_comp _).symm)

omit [∀ F, PreservesFiniteLimits (H.obj F)] in
/-- `h^{n+1}(H(L_{•+1}, -)) ≅ h^{n+2}(H(L_•, -))`. -/
noncomputable def shiftIso {F : C} (P : Resolution F) (n : ℕ) :
    homComplex H P.truncate.L ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) (n + 1) ≅
      homComplex H P.L ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) (n + 2) :=
  Functor.isoWhiskerLeft _ (HomologicalComplex.homologyFunctorIso' C (ComplexShape.up ℕ)
      n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scShiftIso H P n) (ShortComplex.homologyFunctor C) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (HomologicalComplex.homologyFunctorIso' C (ComplexShape.up ℕ)
      (n + 1) (n + 2) (n + 3) (by simp) (by simp)).symm

/-- **Resolutions with `E`-acyclic terms compute `E`**, by dimension shifting: for a resolution
`L_• ⟶ F ⟶ 0` whose terms `L_p` satisfy `E L_p (n + 1) = 0`, natural isomorphisms
`E F i ≅ hⁱ(H(L_•, -))`. -/
noncomputable def isoAux : ∀ (i : ℕ) {F : C} (P : Resolution F)
    (_ : ∀ p n G, IsZero ((E (P.L.X p) (n + 1)).obj G)),
    E F i ≅ homComplex H P.L ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) i
  | 0, _, P, _ => iso0 H E hE hH P
  | 1, _, P, hacyc => iso1 H E hE hH P (hacyc 0 0)
  | n + 2, _, P, hacyc =>
      (δIso H E hE hH P.ses_shortExact n (hacyc 0 n) (hacyc 0 (n + 1))).symm ≪≫
        isoAux (n + 1) P.truncate (fun p => hacyc (p + 1)) ≪≫ shiftIso H P n

end Abstract

end LocallyFreeResolutionExt

/-! ### Sheaf `ℰxt` -/

section Sheaf

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

/- As in `Hartshorne.RingedSpace.SheafExt`, use the preadditive structure coming from the abelian
structure, which is the one Mathlib's derived-functor API is stated with. -/
attribute [local instance 2000] Abelian.toPreadditive

/-- Injective resolutions of module sheaves, as a single constant (see
`Hartshorne.RingedSpace.SheafExtLongExact`). -/
private theorem sheafOfModules_hasInjectiveResolutions' :
    HasInjectiveResolutions (SheafOfModules.{u} (ringCatSheafOf R)) :=
  inferInstance

attribute [local instance 3000] sheafOfModules_hasInjectiveResolutions'

/-- The cochain complex `ℋom(L_•, G)` of a chain complex `L_•` of `𝒪_X`-modules, functorial in
`G`: in degree `p` it is `ℋom(L_p, G)`, with differentials given by precomposition with the
differentials of `L_•`. -/
noncomputable def moduleSheafHomComplex (L : ChainComplex 𝓜 ℕ) : 𝓜 ⥤ CochainComplex 𝓜 ℕ :=
  LocallyFreeResolutionExt.homComplex (moduleSheafHomBifunctor R) L

lemma moduleSheafHomComplex_X (L : ChainComplex 𝓜 ℕ) (G : 𝓜) (p : ℕ) :
    ((moduleSheafHomComplex L).obj G).X p = moduleSheafHom (L.X p) G := rfl

lemma moduleSheafHomComplex_d (L : ChainComplex 𝓜 ℕ) (G : 𝓜) (p : ℕ) :
    ((moduleSheafHomComplex L).obj G).d p (p + 1) = (moduleSheafHomPrecomp (L.d (p + 1) p)).app G :=
  LocallyFreeResolutionExt.homComplex_d _ L G p

/-- **Locally free resolutions compute `ℰxt`** (Hartshorne III.6, Proposition 6.5, p. 234). Let
`L_• ⟶ F ⟶ 0` be a resolution of an `𝒪_X`-module `F` by locally free `𝒪_X`-modules of finite rank,
possibly unbounded to the left, given as a quasi-isomorphism `π : L_• ⟶ F[0]`. Then for every `i`
there is an isomorphism `ℰxtⁱ(F, G) ≅ hⁱ(ℋom(L_•, G))`, natural in the `𝒪_X`-module `G`. -/
noncomputable def sheafExtIsoHomologyOfLocallyFreeResolution {F : 𝓜} (L : ChainComplex 𝓜 ℕ)
    (π : L ⟶ (ChainComplex.single₀ 𝓜).obj F) [QuasiIso π] (hL : ∀ p, IsFiniteLocallyFree (L.X p))
    (i : ℕ) :
    sheafExt F i ≅
      moduleSheafHomComplex L ⋙ HomologicalComplex.homologyFunctor 𝓜 (ComplexShape.up ℕ) i :=
  LocallyFreeResolutionExt.isoAux (moduleSheafHomBifunctor R) sheafExt (fun _ _ => rfl)
    moduleSheafHom_shortExact_of_injective i (LocallyFreeResolutionExt.Resolution.ofQuasiIso L π)
    (fun p n G => isZero_sheafExt_of_isFiniteLocallyFree (hL p) G n.succ_pos)

end Sheaf

end Ringed

end Hartshorne
