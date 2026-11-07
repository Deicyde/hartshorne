/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ModuleSectionsRepresentable
import Hartshorne.RingedSpace.SheafExt
import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# The map from global Ext to global sections of sheaf Ext

Hartshorne, *Algebraic Geometry*, III.6: the natural map of Proposition 6.9 (p. 236), between the
global Ext groups and the global sections of the sheaves `ℰxt` defined on p. 233.

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`, and let `F`, `G` be `𝒪_X`-modules. Global Ext is Mathlib's `Abelian.Ext`, for a
chosen universe `w` and a `HasExt.{w}` instance on the category of `𝒪_X`-modules; sheaf Ext is
`Hartshorne.Ringed.sheafExt`. We construct, for an injective resolution of `G`, the additive map
`Extⁱ(F, G) ⟶ Γ(X, ℰxtⁱ(F, G))`.

For an injective resolution `G ⟶ I^•`, a class in `Extⁱ(F, G)` is represented by a morphism
`f : F ⟶ Iⁱ` with `f ≫ d = 0` (Mathlib's `InjectiveResolution.extMk`). Through the identification
`Hom(F, Iⁱ) ≅ Γ(X, ℋom(F, Iⁱ))`, compatible with the differentials of the global-Hom and sheaf-Hom
complexes, `f` is a global cocycle of `ℋom(F, I^•)`. Global sections over `X` are the morphisms
out of `𝒪_X = j_!(𝒪_X|_X)` (`Hartshorne.moduleSectionsAddEquiv` for the open `X`), so this cocycle
is a morphism `𝒪_X ⟶ ℋom(F, Iⁱ)` into the cycles of the sheaf-Hom complex; its image in the
cohomology sheaf `ℋⁱ(ℋom(F, I^•)) ≅ ℰxtⁱ(F, G)` is the image of the class
(`Hartshorne.Ringed.globalToSheafExtOf_extMk`). Coboundaries go to zero, so this is well defined.

This file constructs the map for a given resolution (`Hartshorne.Ringed.globalToSheafExtOf`) with
its value on representing cocycles (`Hartshorne.Ringed.globalToSheafExtOf_extMk`), the
degree-zero comparison `Hartshorne.extMk_resolutionAugmentation` between cocycle classes and
`Ext.mk₀`, and the contravariant functoriality of `ℰxtⁱ(-, G)` obtained by deriving the
precomposition maps `ℋom(F, -) ⟶ ℋom(F', -)` (`Hartshorne.Ringed.sheafExtMapFst`).

No isomorphism is asserted.
-/

universe w v u

open CategoryTheory Opposite Limits Abelian CochainComplex HomComplex Localization

namespace Hartshorne

section InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The augmentation `Y ⟶ I⁰` of an injective resolution `Y ⟶ I^•`. -/
noncomputable def resolutionAugmentation {Y : C} (I : InjectiveResolution Y) :
    Y ⟶ I.cocomplex.X 0 :=
  I.ι.f 0

@[reassoc (attr := simp)]
lemma resolutionAugmentation_d {Y : C} (I : InjectiveResolution Y) :
    resolutionAugmentation I ≫ I.cocomplex.d 0 1 = 0 :=
  I.ι_f_zero_comp_complex_d

private lemma ι'_f_zero_eq {Y : C} (I : InjectiveResolution Y) :
    I.ι'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom ≫ resolutionAugmentation I ≫
      (I.cochainComplexXIso _ _ (by simp)).inv :=
  I.ι'_f_zero

/-- In degree zero, the cocycle of `Hom(X, I^•)` given by `g : X ⟶ Y` followed by the
augmentation corresponds to the morphism of complexes `X ⟶ I^•` induced by `g`. -/
private lemma fromSingleMk_augmentation {X Y : C} (I : InjectiveResolution Y) (g : X ⟶ Y) :
    Cocycle.fromSingleMk ((g ≫ resolutionAugmentation I) ≫
        (I.cochainComplexXIso ((0 : ℕ) : ℤ) 0 rfl).inv)
      (zero_add _) ((1 : ℕ) : ℤ) (by simp)
      (by rw [I.cochainComplex_d _ _ 0 1 rfl rfl]; simp) =
    Cocycle.equivHomShift (ShiftedHom.mk₀ ((0 : ℕ) : ℤ) (by simp)
      ((singleFunctor C 0).map g ≫ I.ι')) := by
  ext p q hpq
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by simpa using hpq.symm
    simp [Cocycle.equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero 0),
      Cochain.fromSingleMk_v, ShiftedHom.mk₀, ι'_f_zero_eq]
    have h₁ : ((singleFunctor C 0).map g).f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫
          g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).inv :=
      HomologicalComplex.single_map_f_self _ _ g
    have h₂ : ((CategoryTheory.shiftFunctorZero' (CochainComplex C ℤ) (0 : ℤ) rfl).inv.app
        I.cochainComplex).f 0 = 𝟙 _ := by
      simp [CategoryTheory.shiftFunctorZero', shiftFunctorZero_inv_app_f]
    rw [h₁, h₂]
    have aux : ∀ {A P B Q Z : C} (a : A ⟶ P) (g : P ⟶ Q) (e : B ≅ Q) (t : Q ⟶ Z),
        a ≫ g ≫ t = (a ≫ g ≫ e.inv) ≫ (e.hom ≫ t) ≫ 𝟙 Z := by
      intros; simp
    exact aux _ _ _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X p hp).eq_of_src _ _

/-- **Degree-zero Ext classes from an injective resolution.** For an injective resolution
`Y ⟶ I^•` and `g : X ⟶ Y`, the class in `Ext⁰(X, Y)` of the cocycle `X ⟶ Y ⟶ I⁰` of the complex
`Hom(X, I^•)` is the class of `g` under `Hom(X, Y) ≅ Ext⁰(X, Y)`. -/
lemma extMk_resolutionAugmentation [HasExt.{w} C] {X Y : C} (I : InjectiveResolution Y)
    (g : X ⟶ Y) :
    I.extMk (g ≫ resolutionAugmentation I) 1 rfl
      (by rw [Category.assoc, resolutionAugmentation_d, comp_zero]) = Ext.mk₀ g := by
  apply I.extEquivCohomologyClass.injective
  rw [InjectiveResolution.extEquivCohomologyClass_extMk, fromSingleMk_augmentation]
  apply (CohomologyClass.equivOfIsKInjective.{w} (K := (singleFunctor C 0).obj X)
    (L := I.cochainComplex) (n := ((0 : ℕ) : ℤ))).injective
  rw [CohomologyClass.equivOfIsKInjective_apply, CohomologyClass.toSmallShiftedHom_mk,
    AddEquiv.symm_apply_apply]
  change _ = CohomologyClass.equivOfIsKInjective (CohomologyClass.equivOfIsKInjective.symm
    (SmallShiftedHom.postcompEquiv.{w} I.ι' _ (SmallShiftedHom.mk₀.{w} _ ((0 : ℕ) : ℤ)
      (by simp) ((singleFunctor C 0).map g))))
  rw [Equiv.apply_symm_apply, SmallShiftedHom.postcompEquiv_apply]
  have := HasDerivedCategory.standard C
  apply (SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  simp [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_mk]

end InjectiveResolution

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

set_option hygiene false in
/-- The structure sheaf as the `𝒪_X`-module `j_!(𝒪_X|_X)` for the open `X`, which represents
global sections. -/
local notation "𝒪ₓ" => openStructureModule (ringCatSheafOf R) ⊤

/- As in `Hartshorne.RingedSpace.SheafExt`, use the preadditive structure coming from the abelian
structure, which is the one Mathlib's derived-functor and Ext API is stated with. -/
attribute [local instance 2000] Abelian.toPreadditive

/-- The morphisms `F ⟶ M` are the morphisms `𝒪_X ⟶ ℋom(F, M)`: a morphism is a global section of
`ℋom(F, M)`, and global sections are the morphisms out of `𝒪_X`. -/
noncomputable def homEquivStructureHom (F M : 𝓜) : (F ⟶ M) ≃+ (𝒪ₓ ⟶ (moduleSheafHomFunctor F).obj M) :=
  (moduleSheafHomGlobalSectionsAddEquiv F M).symm.trans
    (moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((moduleSheafHomFunctor F).obj M)).symm

lemma moduleSectionsAddEquiv_homEquivStructureHom (F M : 𝓜) (f : F ⟶ M) :
    moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((moduleSheafHomFunctor F).obj M)
        (homEquivStructureHom F M f) =
      (moduleSheafHomGlobalSectionsAddEquiv F M).symm f :=
  AddEquiv.apply_symm_apply _ _

/-- The identification `Hom(F, M) ≅ Hom(𝒪_X, ℋom(F, M))` is natural in both variables. -/
lemma homEquivStructureHom_naturality {F F' M M' : 𝓜} (h : F' ⟶ F) (f : F ⟶ M) (g : M ⟶ M') :
    homEquivStructureHom F' M' (h ≫ f ≫ g) = homEquivStructureHom F M f ≫
      (moduleSheafHomMap h g : (moduleSheafHomFunctor F).obj M ⟶ (moduleSheafHomFunctor F').obj M') := by
  apply (moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((moduleSheafHomFunctor F').obj M')).injective
  have hn := moduleSectionsAddEquiv_naturality (ringCatSheafOf R) ⊤ ((moduleSheafHomFunctor F).obj M)
    ((moduleSheafHomFunctor F').obj M') (homEquivStructureHom F M f) (moduleSheafHomMap h g)
  refine Eq.trans ?_ hn.symm
  rw [moduleSectionsAddEquiv_homEquivStructureHom, moduleSectionsAddEquiv_homEquivStructureHom]
  apply (moduleSheafHomGlobalSectionsAddEquiv F' M').injective
  rw [AddEquiv.apply_symm_apply]
  refine Eq.trans ?_ (moduleSheafHom_global_map h g _).symm
  change h ≫ f ≫ g = h ≫ moduleSheafHomGlobalSectionsAddEquiv F M
    ((moduleSheafHomGlobalSectionsAddEquiv F M).symm f) ≫ g
  rw [AddEquiv.apply_symm_apply]

/-- Precomposition with `h : F' ⟶ F`, as a natural transformation `ℋom(F, -) ⟶ ℋom(F', -)`. -/
noncomputable def moduleSheafHomPrecomp {F F' : 𝓜} (h : F' ⟶ F) :
    moduleSheafHomFunctor F ⟶ moduleSheafHomFunctor F' where
  app G := moduleSheafHomMap h (𝟙 G)
  naturality {G G'} g := by
    apply SheafOfModules.hom_ext
    ext U σ
    change (SheafOfModules.overFunctor _ U.unop).map (𝟙 F') ≫
        ((SheafOfModules.overFunctor _ U.unop).map h ≫ σ ≫
          (SheafOfModules.overFunctor _ U.unop).map (𝟙 G)) ≫
        (SheafOfModules.overFunctor _ U.unop).map g =
      (SheafOfModules.overFunctor _ U.unop).map h ≫
        ((SheafOfModules.overFunctor _ U.unop).map (𝟙 F) ≫ σ ≫
          (SheafOfModules.overFunctor _ U.unop).map g) ≫
        (SheafOfModules.overFunctor _ U.unop).map (𝟙 G')
    obtain ⟨τ, rfl⟩ : ∃ τ : F.over U.unop ⟶ G.over U.unop, τ = σ := ⟨σ, rfl⟩
    simp

lemma moduleSheafHomPrecomp_app {F F' : 𝓜} (h : F' ⟶ F) (G : 𝓜) :
    (moduleSheafHomPrecomp h).app G = moduleSheafHomMap h (𝟙 G) := rfl

/-- **Contravariant functoriality of sheaf Ext.** For `h : F' ⟶ F`, the natural transformation
`ℰxtⁿ(F, -) ⟶ ℰxtⁿ(F', -)` obtained by deriving precomposition `ℋom(F, -) ⟶ ℋom(F', -)`. -/
noncomputable def sheafExtMapFst {F F' : 𝓜} (h : F' ⟶ F) (n : ℕ) : sheafExt F n ⟶ sheafExt F' n :=
  NatTrans.rightDerived (moduleSheafHomPrecomp h) n

/-- The complex `ℋom(F, K^•)` of `𝒪_X`-modules, for a complex `K^•` of `𝒪_X`-modules. -/
noncomputable abbrev sheafHomComplex (F : 𝓜) (K : CochainComplex 𝓜 ℕ) : CochainComplex 𝓜 ℕ :=
  ((moduleSheafHomFunctor F).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- A morphism `f : F ⟶ Kᵖ`, a degree-`p` cochain of the global-Hom complex `Hom(F, K^•)`, as a
global section of the degree-`p` term of the sheaf-Hom complex `ℋom(F, K^•)`, that is, a morphism
`𝒪_X ⟶ ℋom(F, Kᵖ)`. -/
noncomputable def sheafHomCochain (F : 𝓜) (K : CochainComplex 𝓜 ℕ) (p : ℕ) (f : F ⟶ K.X p) :
    𝒪ₓ ⟶ (sheafHomComplex F K).X p :=
  homEquivStructureHom F (K.X p) f

lemma sheafHomCochain_add (F : 𝓜) (K : CochainComplex 𝓜 ℕ) (p : ℕ) (f₁ f₂ : F ⟶ K.X p) :
    sheafHomCochain F K p (f₁ + f₂) = sheafHomCochain F K p f₁ + sheafHomCochain F K p f₂ :=
  map_add (homEquivStructureHom F (K.X p)) f₁ f₂

/-- The identification of cochains is compatible with the differentials of the global-Hom and
sheaf-Hom complexes. -/
lemma sheafHomCochain_comp_d (F : 𝓜) (K : CochainComplex 𝓜 ℕ) {p q : ℕ} (f : F ⟶ K.X p) :
    sheafHomCochain F K q (f ≫ K.d p q) =
      sheafHomCochain F K p f ≫ (sheafHomComplex F K).d p q := by
  have h := homEquivStructureHom_naturality (𝟙 F) f (K.d p q)
  rw [Category.id_comp] at h
  exact h

/-- The identification of cochains is natural with respect to morphisms of complexes. -/
lemma sheafHomCochain_comp_f (F : 𝓜) {K L : CochainComplex 𝓜 ℕ} (φ : K ⟶ L) {p : ℕ}
    (f : F ⟶ K.X p) :
    sheafHomCochain F L p (f ≫ φ.f p) =
      sheafHomCochain F K p f ≫
        (((moduleSheafHomFunctor F).mapHomologicalComplex (ComplexShape.up ℕ)).map φ).f p := by
  have h := homEquivStructureHom_naturality (𝟙 F) f (φ.f p)
  rw [Category.id_comp] at h
  exact h

/-- The identification of cochains is natural with respect to the first variable. -/
lemma sheafHomCochain_precomp {F F' : 𝓜} (h : F' ⟶ F) (K : CochainComplex 𝓜 ℕ) {p : ℕ}
    (f : F ⟶ K.X p) :
    sheafHomCochain F' K p (h ≫ f) =
      sheafHomCochain F K p f ≫
        ((NatTrans.mapHomologicalComplex (moduleSheafHomPrecomp h) (ComplexShape.up ℕ)).app K).f
          p := by
  have h' := homEquivStructureHom_naturality h f (𝟙 (K.X p))
  rw [Category.comp_id] at h'
  exact h'

section

variable (F : 𝓜) {G : 𝓜} (I : InjectiveResolution G) (n : ℕ)

/-- The identification `ℰxtⁿ(F, G) ≅ ℋⁿ(ℋom(F, I^•))` of `Hartshorne.Ringed.sheafExtIsoHomology`,
with its target written as the homology of `sheafHomComplex F I^•`. -/
noncomputable def sheafExtIsoSheafHomComplexHomology :
    (sheafExt F n).obj G ≅ (sheafHomComplex F I.cocomplex).homology n :=
  sheafExtIsoHomology F I n

private lemma sheafHomCochain_comp_d_eq_zero {f : F ⟶ I.cocomplex.X n}
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    sheafHomCochain F I.cocomplex n f ≫ (sheafHomComplex F I.cocomplex).d n (n + 1) = 0 := by
  rw [← sheafHomCochain_comp_d, hf]
  exact map_zero (homEquivStructureHom F _)

/-- The morphism `𝒪_X ⟶ ℰxtⁿ(F, G)` (a global section of `ℰxtⁿ(F, G)`) defined by a cocycle
`f : F ⟶ Iⁿ` of the global-Hom complex `Hom(F, I^•)`: viewed as a global cocycle of the sheaf-Hom
complex `ℋom(F, I^•)`, it defines a global section of the cohomology sheaf
`ℋⁿ(ℋom(F, I^•)) ≅ ℰxtⁿ(F, G)`. -/
noncomputable def cocycleSheafExtClass (f : F ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) : 𝒪ₓ ⟶ (sheafExt F n).obj G :=
  (sheafHomComplex F I.cocomplex).liftCycles (sheafHomCochain F I.cocomplex n f) (n + 1)
      (by simp) (sheafHomCochain_comp_d_eq_zero F I n hf) ≫
    (sheafHomComplex F I.cocomplex).homologyπ n ≫ (sheafExtIsoSheafHomComplexHomology F I n).inv

variable {F I n}

lemma cocycleSheafExtClass_congr {f₁ f₂ : F ⟶ I.cocomplex.X n} (h : f₁ = f₂)
    (hf₁ : f₁ ≫ I.cocomplex.d n (n + 1) = 0) (hf₂ : f₂ ≫ I.cocomplex.d n (n + 1) = 0) :
    cocycleSheafExtClass F I n f₁ hf₁ = cocycleSheafExtClass F I n f₂ hf₂ := by
  subst h
  rfl

lemma cocycleSheafExtClass_add {f₁ f₂ : F ⟶ I.cocomplex.X n}
    (hf₁ : f₁ ≫ I.cocomplex.d n (n + 1) = 0) (hf₂ : f₂ ≫ I.cocomplex.d n (n + 1) = 0)
    (hf : (f₁ + f₂) ≫ I.cocomplex.d n (n + 1) = 0) :
    cocycleSheafExtClass F I n (f₁ + f₂) hf =
      cocycleSheafExtClass F I n f₁ hf₁ + cocycleSheafExtClass F I n f₂ hf₂ := by
  have hlift : (sheafHomComplex F I.cocomplex).liftCycles (sheafHomCochain F I.cocomplex n (f₁ + f₂))
      (n + 1) (by simp) (sheafHomCochain_comp_d_eq_zero F I n hf) =
      (sheafHomComplex F I.cocomplex).liftCycles (sheafHomCochain F I.cocomplex n f₁)
        (n + 1) (by simp) (sheafHomCochain_comp_d_eq_zero F I n hf₁) +
      (sheafHomComplex F I.cocomplex).liftCycles (sheafHomCochain F I.cocomplex n f₂)
        (n + 1) (by simp) (sheafHomCochain_comp_d_eq_zero F I n hf₂) := by
    rw [← cancel_mono ((sheafHomComplex F I.cocomplex).iCycles n),
      CategoryTheory.Preadditive.add_comp, HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i, sheafHomCochain_add]
  rw [cocycleSheafExtClass, cocycleSheafExtClass, cocycleSheafExtClass, hlift,
    CategoryTheory.Preadditive.add_comp]

lemma cocycleSheafExtClass_zero :
    cocycleSheafExtClass F I n 0 zero_comp = 0 := by
  have h := cocycleSheafExtClass_add (F := F) (I := I) (n := n) (f₁ := 0) (f₂ := 0) zero_comp
    zero_comp (by rw [add_zero, zero_comp])
  rw [cocycleSheafExtClass_congr (add_zero 0) _ zero_comp] at h
  simpa using h.symm

/-- The class of a coboundary `g ≫ d` vanishes. -/
lemma cocycleSheafExtClass_comp_d {p : ℕ} (g : F ⟶ I.cocomplex.X p)
    (hf : (g ≫ I.cocomplex.d p n) ≫ I.cocomplex.d n (n + 1) = 0) :
    cocycleSheafExtClass F I n (g ≫ I.cocomplex.d p n) hf = 0 := by
  rw [cocycleSheafExtClass, ← Category.assoc,
    HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _
      (sheafHomCochain F I.cocomplex p g) (sheafHomCochain_comp_d F I.cocomplex g), zero_comp]

variable [HasExt.{w} 𝓜]

/-- A cocycle whose Ext class vanishes has vanishing class in `ℰxtⁿ(F, G)`. -/
lemma cocycleSheafExtClass_eq_zero_of_extMk_eq_zero {f : F ⟶ I.cocomplex.X n}
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) (h : I.extMk f (n + 1) rfl hf = 0) :
    cocycleSheafExtClass F I n f hf = 0 := by
  cases n with
  | zero =>
    obtain rfl : f = 0 := by
      rw [← I.extEquivCohomologyClass.apply_eq_iff_eq, I.extEquivCohomologyClass_extMk,
        I.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff,
        Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by simp)] at h
      obtain ⟨g, hg⟩ := h
      have hz : IsZero (I.cochainComplex.X (-1)) :=
        CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by lia)
      obtain rfl : g = 0 := hz.eq_of_tgt _ _
      rw [zero_comp] at hg
      exact (cancel_mono (I.cochainComplexXIso _ 0 rfl).inv).mp (hg.symm.trans zero_comp.symm)
    exact cocycleSheafExtClass_zero
  | succ p =>
    obtain ⟨g, rfl⟩ := (I.extMk_eq_zero_iff f _ rfl hf p rfl).mp h
    exact cocycleSheafExtClass_comp_d g hf

lemma cocycleSheafExtClass_eq_of_extMk_eq {f₁ f₂ : F ⟶ I.cocomplex.X n}
    (hf₁ : f₁ ≫ I.cocomplex.d n (n + 1) = 0) (hf₂ : f₂ ≫ I.cocomplex.d n (n + 1) = 0)
    (h : I.extMk f₁ (n + 1) rfl hf₁ = I.extMk f₂ (n + 1) rfl hf₂) :
    cocycleSheafExtClass F I n f₁ hf₁ = cocycleSheafExtClass F I n f₂ hf₂ := by
  have hd : (f₁ - f₂) ≫ I.cocomplex.d n (n + 1) = 0 := by
    rw [CategoryTheory.Preadditive.sub_comp, hf₁, hf₂, sub_zero]
  have h' := cocycleSheafExtClass_eq_zero_of_extMk_eq_zero hd
    (by rw [← I.sub_extMk f₁ f₂ (n + 1) rfl hf₁ hf₂, h, sub_self])
  have hs : (f₁ - f₂ + f₂) ≫ I.cocomplex.d n (n + 1) = 0 := by
    rw [CategoryTheory.Preadditive.add_comp, hd, hf₂, add_zero]
  rw [cocycleSheafExtClass_congr (sub_add_cancel f₁ f₂).symm hf₁ hs,
    cocycleSheafExtClass_add hd hf₂ hs, h', zero_add]

variable (F I n) in
/-- The function underlying `globalToSheafExtOf`, through a choice of representing cocycles. -/
private noncomputable def globalToSheafExtFun (e : Ext.{w} F G n) :
    ((sheafExt F n).obj G).val.obj (op ⊤) :=
  moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ _
    (cocycleSheafExtClass F I n (I.extMk_surjective e (n + 1) rfl).choose
      (I.extMk_surjective e (n + 1) rfl).choose_spec.choose)

private lemma globalToSheafExtFun_extMk (f : F ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    globalToSheafExtFun F I n (I.extMk f (n + 1) rfl hf) =
      moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ _ (cocycleSheafExtClass F I n f hf) := by
  have h := (I.extMk_surjective (I.extMk f (n + 1) rfl hf) (n + 1) rfl).choose_spec
  exact congrArg (moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((sheafExt F n).obj G))
    (cocycleSheafExtClass_eq_of_extMk_eq h.choose hf h.choose_spec)

variable (F I n) in
/-- **The global-to-sheaf Ext map, computed from an injective resolution.** For an injective
resolution `G ⟶ I^•`, the additive map `Extⁿ(F, G) ⟶ Γ(X, ℰxtⁿ(F, G))` sending the class of a
cocycle `f : F ⟶ Iⁿ` of `Hom(F, I^•)` to the class of the corresponding global cocycle of
`ℋom(F, I^•)` in `Γ(X, ℋⁿ(ℋom(F, I^•))) ≅ Γ(X, ℰxtⁿ(F, G))`. -/
noncomputable def globalToSheafExtOf :
    Ext.{w} F G n →+ ((sheafExt F n).obj G).val.obj (op ⊤) where
  toFun := globalToSheafExtFun F I n
  map_zero' := by
    have h0 : (0 : Ext.{w} F G n) = I.extMk 0 (n + 1) rfl zero_comp := (I.extMk_zero _ _).symm
    rw [h0, globalToSheafExtFun_extMk, cocycleSheafExtClass_zero, map_zero]
  map_add' e₁ e₂ := by
    obtain ⟨f₁, hf₁, rfl⟩ := I.extMk_surjective e₁ (n + 1) rfl
    obtain ⟨f₂, hf₂, rfl⟩ := I.extMk_surjective e₂ (n + 1) rfl
    rw [I.add_extMk, globalToSheafExtFun_extMk, globalToSheafExtFun_extMk,
      globalToSheafExtFun_extMk, cocycleSheafExtClass_add hf₁ hf₂, map_add]

/-- On the class of a cocycle `f : F ⟶ Iⁿ`, the map computed from the resolution `I` is the global
section defined by `f` as a global cocycle of `ℋom(F, I^•)`. -/
lemma globalToSheafExtOf_extMk (f : F ⟶ I.cocomplex.X n) (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    globalToSheafExtOf F I n (I.extMk f (n + 1) rfl hf) =
      moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ _ (cocycleSheafExtClass F I n f hf) :=
  globalToSheafExtFun_extMk f hf

end

end Ringed

end Hartshorne
