/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ModuleSectionsRepresentable
import Hartshorne.RingedSpace.SheafExtContravariant
import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# The map from global Ext to global sections of sheaf Ext

Hartshorne, *Algebraic Geometry*, III.6: the natural map of Proposition 6.9 (p. 236), between the
global Ext groups and the global sections of the sheaves `ℰxt` defined on p. 233.

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`, and let `F`, `G` be `𝒪_X`-modules. Global Ext is Mathlib's `Abelian.Ext`, for a
chosen universe `w` and a `HasExt.{w}` instance on the category of `𝒪_X`-modules; sheaf Ext is
`Hartshorne.Ringed.sheafExt`. We construct the additive map
`Extⁱ(F, G) ⟶ Γ(X, ℰxtⁱ(F, G))` (`Hartshorne.Ringed.globalToSheafExt`).

For an injective resolution `G ⟶ I^•`, a class in `Extⁱ(F, G)` is represented by a morphism
`f : F ⟶ Iⁱ` with `f ≫ d = 0` (Mathlib's `InjectiveResolution.extMk`). Through the identification
`Hom(F, Iⁱ) ≅ Γ(X, ℋom(F, Iⁱ))`, compatible with the differentials of the global-Hom and sheaf-Hom
complexes, `f` is a global cocycle of `ℋom(F, I^•)`. Global sections over `X` are the morphisms
out of `𝒪_X = j_!(𝒪_X|_X)` (`Hartshorne.moduleSectionsAddEquiv` for the open `X`), so this cocycle
is a morphism `𝒪_X ⟶ ℋom(F, Iⁱ)` into the cycles of the sheaf-Hom complex; its image in the
cohomology sheaf `ℋⁱ(ℋom(F, I^•)) ≅ ℰxtⁱ(F, G)` is the image of the class
(`Hartshorne.Ringed.globalToSheafExt_extMk`, for any injective resolution). Coboundaries go to
zero, so this is well defined, and the result does not depend on the resolution. In degree zero
the map is the identification `Hom(F, G) ≅ Γ(X, ℋom(F, G)) ≅ Γ(X, ℰxt⁰(F, G))`
(`Hartshorne.Ringed.globalToSheafExt_mk₀`), and it is natural in `G`
(`Hartshorne.Ringed.globalToSheafExt_comp_mk₀`) and in `F`
(`Hartshorne.Ringed.globalToSheafExt_mk₀_comp`). No isomorphism is asserted.

## Implementation note

The homological algebra is done once for an abstract additive functor `H` on an abelian
category, an object `O` and an additive identification `e : Hom(F, M) ≅ Hom(O, H M)` natural in
`M` (namespace `Hartshorne.ExtToDerived`), with the derived functors replaced by functors `E` equal
to them. It is then specialized to `H = ℋom(F, -)`, `O = 𝒪_X` and `E = ℰxtⁿ(F, -)`. Working
abstractly keeps the kernel from unfolding the abelian structure of the category of
`𝒪_X`-modules, which makes every concrete statement mixing the complex `ℋom(F, I^•)` with these
identifications slow to check.
-/

universe w v u

open CategoryTheory Opposite Limits Abelian CochainComplex HomComplex

namespace Hartshorne

section InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma ι'_f_zero_eq {Y : C} (I : InjectiveResolution Y) :
    I.ι'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom ≫ RightDerivedLES.aug I ≫
      (I.cochainComplexXIso _ _ (by simp)).inv :=
  I.ι'_f_zero

/-- In degree zero, the cocycle of `Hom(X, I^•)` given by `g : X ⟶ Y` followed by the
augmentation corresponds to the morphism of complexes `X ⟶ I^•` induced by `g`. -/
private lemma fromSingleMk_aug {X Y : C} (I : InjectiveResolution Y) (g : X ⟶ Y) :
    Cocycle.fromSingleMk ((g ≫ RightDerivedLES.aug I) ≫
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

open Localization in
/-- **Degree-zero Ext classes from an injective resolution.** For an injective resolution
`Y ⟶ I^•` and `g : X ⟶ Y`, the class in `Ext⁰(X, Y)` of the cocycle `X ⟶ Y ⟶ I⁰` of the complex
`Hom(X, I^•)` is the class of `g` under `Hom(X, Y) ≅ Ext⁰(X, Y)`. -/
lemma extMk_aug [HasExt.{w} C] {X Y : C} (I : InjectiveResolution Y) (g : X ⟶ Y) :
    I.extMk (g ≫ RightDerivedLES.aug I) 1 rfl
      (by rw [Category.assoc, RightDerivedLES.aug_d, comp_zero]) = Ext.mk₀ g := by
  apply I.extEquivCohomologyClass.injective
  rw [InjectiveResolution.extEquivCohomologyClass_extMk, fromSingleMk_aug]
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

/-! ### The map from Ext to morphisms into derived functors, abstractly

Let `H : C ⥤ C` be an additive functor on an abelian category, `O` and `F` objects of `C` and
`e : Hom(F, M) ≅ Hom(O, H M)` additive identifications, natural in `M`. For an injective resolution
`G ⟶ I^•`, a cocycle `f : F ⟶ Iⁿ` of `Hom(F, I^•)` gives a cocycle `e f : O ⟶ H(Iⁿ)` of `H(I^•)`,
hence a morphism `O ⟶ Hⁿ(H(I^•)) ≅ (Rⁿ H)(G)`; this defines an additive map
`Extⁿ(F, G) ⟶ Hom(O, (Rⁿ H)(G))`. -/

namespace ExtToDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  (H : C ⥤ C) [H.Additive] {O F : C} (e : ∀ M, (F ⟶ M) ≃+ (O ⟶ H.obj M))
  (he : ∀ {M M' : C} (f : F ⟶ M) (g : M ⟶ M'), e M' (f ≫ g) = e M f ≫ H.map g)

/-- A morphism `f : F ⟶ Kᵖ` as the morphism `O ⟶ H(Kᵖ)` given by `e`, with its target written as
the degree-`p` term of the complex `H(K^•)`. -/
noncomputable def cochain (K : CochainComplex C ℕ) (p : ℕ) :
    (F ⟶ K.X p) ≃+ (O ⟶ ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X p) :=
  e (K.X p)

omit [HasInjectiveResolutions C] in
include he in
lemma cochain_comp_d (K : CochainComplex C ℕ) {p q : ℕ} (f : F ⟶ K.X p) :
    cochain H e K q (f ≫ K.d p q) =
      cochain H e K p f ≫ ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).d p q :=
  he f (K.d p q)

omit [HasInjectiveResolutions C] in
include he in
lemma cochain_comp_f {K L : CochainComplex C ℕ} (φ : K ⟶ L) {p : ℕ} (f : F ⟶ K.X p) :
    cochain H e L p (f ≫ φ.f p) =
      cochain H e K p f ≫ ((H.mapHomologicalComplex (ComplexShape.up ℕ)).map φ).f p :=
  he f (φ.f p)

section

variable {G : C} (I : InjectiveResolution G) (n : ℕ) (E : C ⥤ C) (hE : H.rightDerived n = E)

omit [HasInjectiveResolutions C] in
include he in
lemma cochain_comp_d_eq_zero {f : F ⟶ I.cocomplex.X n} (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    cochain H e I.cocomplex n f ≫
      ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d n (n + 1) = 0 := by
  rw [← cochain_comp_d H e he, hf, map_zero]

/-- The morphism `O ⟶ E(G)` defined by a cocycle `f : F ⟶ Iⁿ`: the class of the cocycle `e f` of
`H(I^•)` in `Hⁿ(H(I^•)) ≅ (Rⁿ H)(G) = E(G)`. -/
noncomputable def cocycleClass (f : F ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) : O ⟶ E.obj G :=
  ((H.mapHomologicalComplex _).obj I.cocomplex).liftCycles (cochain H e I.cocomplex n f) (n + 1)
      (by simp) (cochain_comp_d_eq_zero H e he I n hf) ≫
    ((H.mapHomologicalComplex _).obj I.cocomplex).homologyπ n ≫
      (RightDerivedLES.isoH H I n).inv ≫ eqToHom (Functor.congr_obj hE G)

variable {I n}

lemma cocycleClass_congr {f₁ f₂ : F ⟶ I.cocomplex.X n} (h : f₁ = f₂)
    (hf₁ : f₁ ≫ I.cocomplex.d n (n + 1) = 0) (hf₂ : f₂ ≫ I.cocomplex.d n (n + 1) = 0) :
    cocycleClass H e he I n E hE f₁ hf₁ = cocycleClass H e he I n E hE f₂ hf₂ := by
  subst h
  rfl

lemma cocycleClass_add {f₁ f₂ : F ⟶ I.cocomplex.X n}
    (hf₁ : f₁ ≫ I.cocomplex.d n (n + 1) = 0) (hf₂ : f₂ ≫ I.cocomplex.d n (n + 1) = 0)
    (hf : (f₁ + f₂) ≫ I.cocomplex.d n (n + 1) = 0) :
    cocycleClass H e he I n E hE (f₁ + f₂) hf =
      cocycleClass H e he I n E hE f₁ hf₁ + cocycleClass H e he I n E hE f₂ hf₂ := by
  have hlift : ((H.mapHomologicalComplex _).obj I.cocomplex).liftCycles
      (cochain H e I.cocomplex n (f₁ + f₂)) (n + 1) (by simp)
      (cochain_comp_d_eq_zero H e he I n hf) =
      ((H.mapHomologicalComplex _).obj I.cocomplex).liftCycles (cochain H e I.cocomplex n f₁)
        (n + 1) (by simp) (cochain_comp_d_eq_zero H e he I n hf₁) +
      ((H.mapHomologicalComplex _).obj I.cocomplex).liftCycles (cochain H e I.cocomplex n f₂)
        (n + 1) (by simp) (cochain_comp_d_eq_zero H e he I n hf₂) := by
    rw [← cancel_mono (((H.mapHomologicalComplex _).obj I.cocomplex).iCycles n),
      Preadditive.add_comp, HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i, map_add]
  rw [cocycleClass, cocycleClass, cocycleClass, hlift, Preadditive.add_comp]

lemma cocycleClass_zero :
    cocycleClass H e he I n E hE 0 zero_comp = 0 := by
  have h := cocycleClass_add H e he E hE (I := I) (n := n) (f₁ := 0) (f₂ := 0) zero_comp
    zero_comp (by rw [add_zero, zero_comp])
  rw [cocycleClass_congr H e he E hE (add_zero 0) _ zero_comp] at h
  simpa using h.symm

/-- The class of a coboundary `g ≫ d` vanishes. -/
lemma cocycleClass_comp_d {p : ℕ} (g : F ⟶ I.cocomplex.X p)
    (hf : (g ≫ I.cocomplex.d p n) ≫ I.cocomplex.d n (n + 1) = 0) :
    cocycleClass H e he I n E hE (g ≫ I.cocomplex.d p n) hf = 0 := by
  rw [cocycleClass, ← Category.assoc,
    HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _
      (cochain H e I.cocomplex p g) (cochain_comp_d H e he I.cocomplex g), zero_comp]

variable [HasExt.{w} C]

/-- A cocycle whose Ext class vanishes has vanishing class in `E(G)`. -/
lemma cocycleClass_eq_zero_of_extMk_eq_zero {f : F ⟶ I.cocomplex.X n}
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) (h : I.extMk f (n + 1) rfl hf = 0) :
    cocycleClass H e he I n E hE f hf = 0 := by
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
    exact cocycleClass_zero H e he E hE
  | succ p =>
    obtain ⟨g, rfl⟩ := (I.extMk_eq_zero_iff f _ rfl hf p rfl).mp h
    exact cocycleClass_comp_d H e he E hE g hf

lemma cocycleClass_eq_of_extMk_eq {f₁ f₂ : F ⟶ I.cocomplex.X n}
    (hf₁ : f₁ ≫ I.cocomplex.d n (n + 1) = 0) (hf₂ : f₂ ≫ I.cocomplex.d n (n + 1) = 0)
    (h : I.extMk f₁ (n + 1) rfl hf₁ = I.extMk f₂ (n + 1) rfl hf₂) :
    cocycleClass H e he I n E hE f₁ hf₁ = cocycleClass H e he I n E hE f₂ hf₂ := by
  have hd : (f₁ - f₂) ≫ I.cocomplex.d n (n + 1) = 0 := by
    rw [Preadditive.sub_comp, hf₁, hf₂, sub_zero]
  have h' := cocycleClass_eq_zero_of_extMk_eq_zero H e he E hE hd
    (by rw [← I.sub_extMk f₁ f₂ (n + 1) rfl hf₁ hf₂, h, sub_self])
  have hs : (f₁ - f₂ + f₂) ≫ I.cocomplex.d n (n + 1) = 0 := by
    rw [Preadditive.add_comp, hd, hf₂, add_zero]
  rw [cocycleClass_congr H e he E hE (sub_add_cancel f₁ f₂).symm hf₁ hs,
    cocycleClass_add H e he E hE hd hf₂ hs, h', zero_add]

variable (I n) in
/-- The function underlying `toDerived`, through a choice of representing cocycles. -/
private noncomputable def toDerivedFun (x : Ext.{w} F G n) : O ⟶ E.obj G :=
  cocycleClass H e he I n E hE (I.extMk_surjective x (n + 1) rfl).choose
    (I.extMk_surjective x (n + 1) rfl).choose_spec.choose

private lemma toDerivedFun_extMk (f : F ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    toDerivedFun H e he I n E hE (I.extMk f (n + 1) rfl hf) =
      cocycleClass H e he I n E hE f hf := by
  have h := (I.extMk_surjective (I.extMk f (n + 1) rfl hf) (n + 1) rfl).choose_spec
  exact cocycleClass_eq_of_extMk_eq H e he E hE h.choose hf h.choose_spec

variable (I n) in
/-- The additive map `Extⁿ(F, G) ⟶ Hom(O, E(G))` computed from the injective resolution `I`: the
class of a cocycle `f` goes to `cocycleClass f`. -/
noncomputable def toDerived : Ext.{w} F G n →+ (O ⟶ E.obj G) where
  toFun := toDerivedFun H e he I n E hE
  map_zero' := by
    have h0 : (0 : Ext.{w} F G n) = I.extMk 0 (n + 1) rfl zero_comp := (I.extMk_zero _ _).symm
    rw [h0, toDerivedFun_extMk, cocycleClass_zero]
  map_add' x₁ x₂ := by
    obtain ⟨f₁, hf₁, rfl⟩ := I.extMk_surjective x₁ (n + 1) rfl
    obtain ⟨f₂, hf₂, rfl⟩ := I.extMk_surjective x₂ (n + 1) rfl
    rw [I.add_extMk, toDerivedFun_extMk, toDerivedFun_extMk, toDerivedFun_extMk,
      cocycleClass_add H e he E hE hf₁ hf₂]

lemma toDerived_extMk (f : F ⟶ I.cocomplex.X n) (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    toDerived H e he I n E hE (I.extMk f (n + 1) rfl hf) = cocycleClass H e he I n E hE f hf :=
  toDerivedFun_extMk H e he E hE f hf

/-- Naturality in the second variable. -/
lemma toDerived_comp_mk₀ {G' : C} (g : G ⟶ G') (I' : InjectiveResolution G')
    (x : Ext.{w} F G n) :
    toDerived H e he I' n E hE (x.comp (Ext.mk₀ g) (add_zero n)) =
      toDerived H e he I n E hE x ≫ E.map g := by
  subst hE
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  have comm := InjectiveResolution.desc_commutes_zero g I' I
  let φ : InjectiveResolution.Hom I I' g :=
    ⟨InjectiveResolution.desc g I' I, comm.trans (by simp)⟩
  rw [InjectiveResolution.extMk_comp_mk₀ f (n + 1) rfl hf φ, toDerived_extMk, toDerived_extMk,
    cocycleClass, cocycleClass]
  simp only [eqToHom_refl, Category.comp_id, Category.assoc]
  rw [RightDerivedLES.isoH_inv_comp_map H g I I' φ.hom comm n,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  congr 1
  rw [← cancel_mono (((H.mapHomologicalComplex _).obj I'.cocomplex).iCycles n),
    HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  exact cochain_comp_f H e he φ.hom f

/-- The map does not depend on the resolution. -/
lemma toDerived_eq (I' : InjectiveResolution G) :
    toDerived H e he I n E hE = toDerived H e he I' n E hE := by
  ext x
  have h := toDerived_comp_mk₀ H e he E hE (I := I) (𝟙 G) I' x
  rw [Ext.comp_mk₀_id, CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.symm

/-- Degree zero: the class of `g : F ⟶ G` goes to `e g` followed by `H(G) ⟶ (R⁰ H)(G)`. -/
lemma toDerived_mk₀ (E : C ⥤ C) (hE : H.rightDerived 0 = E) (g : F ⟶ G) :
    toDerived H e he I 0 E hE (Ext.mk₀ g) =
      e G g ≫ H.toRightDerivedZero.app G ≫ eqToHom (Functor.congr_obj hE G) := by
  subst hE
  have hf : (g ≫ RightDerivedLES.aug I) ≫ I.cocomplex.d 0 (0 + 1) = 0 := by
    rw [Category.assoc, RightDerivedLES.aug_d, comp_zero]
  have h' : I.extMk (g ≫ RightDerivedLES.aug I) (0 + 1) rfl hf = Ext.mk₀ g := extMk_aug I g
  have hl : ((H.mapHomologicalComplex _).obj I.cocomplex).liftCycles
      (cochain H e I.cocomplex 0 (g ≫ RightDerivedLES.aug I)) (0 + 1) (by simp)
      (cochain_comp_d_eq_zero H e he I 0 hf) = e G g ≫ I.toRightDerivedZero' H := by
    rw [← cancel_mono (((H.mapHomologicalComplex _).obj I.cocomplex).iCycles 0),
      HomologicalComplex.liftCycles_i, Category.assoc,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    exact he g (RightDerivedLES.aug I)
  rw [← h', toDerived_extMk, cocycleClass, I.toRightDerivedZero_eq H, reassoc_of% hl]
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end

/-- Naturality in the first variable: for `h : F' ⟶ F`, a natural transformation `α : H ⟶ H'`
compatible with the identifications `e`, `e'` and precomposition with `h` intertwines the maps
for `F` and `F'` with the map induced by `α` on the cohomology of `H(I^•)` and `H'(I^•)`. -/
lemma toDerived_mk₀_comp [HasExt.{w} C] {F' : C} (h : F' ⟶ F) (H' : C ⥤ C) [H'.Additive]
    (e' : ∀ M, (F' ⟶ M) ≃+ (O ⟶ H'.obj M))
    (he' : ∀ {M M' : C} (f : F' ⟶ M) (g : M ⟶ M'), e' M' (f ≫ g) = e' M f ≫ H'.map g)
    (α : H ⟶ H') (hα : ∀ {M : C} (f : F ⟶ M), e' M (h ≫ f) = e M f ≫ α.app M)
    {G : C} (I : InjectiveResolution G) (n : ℕ) (E E' : C ⥤ C) (hE : H.rightDerived n = E)
    (hE' : H'.rightDerived n = E') (x : Ext.{w} F G n) :
    toDerived H' e' he' I n E' hE' ((Ext.mk₀ h).comp x (zero_add n)) =
      toDerived H e he I n E hE x ≫ eqToHom (Functor.congr_obj hE.symm G) ≫
        (RightDerivedLES.isoH H I n).hom ≫
          HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α _).app I.cocomplex) n ≫
            (RightDerivedLES.isoH H' I n).inv ≫ eqToHom (Functor.congr_obj hE' G) := by
  subst hE hE'
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  rw [InjectiveResolution.mk₀_comp_extMk, toDerived_extMk, toDerived_extMk, cocycleClass,
    cocycleClass]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  congr 1
  rw [← cancel_mono (((H'.mapHomologicalComplex _).obj I.cocomplex).iCycles n),
    HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  exact hα f

/-- Naturality in the first variable for a bifunctor `B` (as `ℋom`) and functors `E F n` equal to
the right derived functors of `B(F, -)`, computed with the chosen resolution of `G`: the maps for
`F` and `F'` are intertwined by the map `E F n G ⟶ E F' n G` induced by `h : F' ⟶ F`
(`Hartshorne.Ringed.SheafExtContravariant.extMap`). -/
lemma toDerived_mk₀_comp_extMap [HasExt.{w} C] (B : Cᵒᵖ ⥤ C ⥤ C)
    [∀ F, (B.obj F).Additive] (E : C → ℕ → C ⥤ C)
    (hE : ∀ F n, (B.obj (op F)).rightDerived n = E F n)
    (e : ∀ F M, (F ⟶ M) ≃+ (O ⟶ (B.obj (op F)).obj M))
    (he : ∀ F {M M' : C} (f : F ⟶ M) (g : M ⟶ M'),
      e F M' (f ≫ g) = e F M f ≫ (B.obj (op F)).map g)
    (hB : ∀ {F F' M : C} (h : F' ⟶ F) (f : F ⟶ M), e F' M (h ≫ f) = e F M f ≫ (B.map h.op).app M)
    {F' G : C} (h : F' ⟶ F) (n : ℕ) (x : Ext.{w} F G n) :
    toDerived (B.obj (op F')) (e F') (he F') (injectiveResolution G) n (E F' n) (hE F' n)
        ((Ext.mk₀ h).comp x (zero_add n)) =
      toDerived (B.obj (op F)) (e F) (he F) (injectiveResolution G) n (E F n) (hE F n) x ≫
        Ringed.SheafExtContravariant.extMap B E hE h G n := by
  rw [toDerived_mk₀_comp (B.obj (op F)) (e F) (he F) h (B.obj (op F')) (e F') (he F')
    (B.map h.op) (fun f ↦ hB h f) (injectiveResolution G) n (E F n) (E F' n) (hE F n) (hE F' n),
    Ringed.SheafExtContravariant.extMap_eq,
    Ringed.SheafExtContravariant.isoE, Ringed.SheafExtContravariant.isoE, Iso.trans_hom,
    Iso.trans_inv, eqToIso.hom, eqToIso.inv]
  simp only [Category.assoc]

end ExtToDerived

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

/-- The additivity of `ℋom(F, -)`, stated for the preadditive structure underlying the abelian
structure (see `Hartshorne.RingedSpace.SheafExtContravariant`). -/
private theorem moduleSheafHomFunctor_additive' (F : 𝓜) :
    @Functor.Additive _ _ _ _ (@Abelian.toPreadditive _ _ sheafOfModules_abelian)
      (@Abelian.toPreadditive _ _ sheafOfModules_abelian) (moduleSheafHomFunctor F) :=
  moduleSheafHomFunctor_additive F

attribute [local instance 3000] moduleSheafHomFunctor_additive'

/-- The morphisms `F ⟶ M` are the morphisms `𝒪_X ⟶ ℋom(F, M)`: a morphism is a global section of
`ℋom(F, M)`, and global sections are the morphisms out of `𝒪_X`. -/
noncomputable def homEquivStructureHom (F M : 𝓜) :
    (F ⟶ M) ≃+ (𝒪ₓ ⟶ (moduleSheafHomFunctor F).obj M) :=
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
      (moduleSheafHomMap h g :
        (moduleSheafHomFunctor F).obj M ⟶ (moduleSheafHomFunctor F').obj M') := by
  apply (moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((moduleSheafHomFunctor F').obj M')).injective
  have hn := moduleSectionsAddEquiv_naturality (ringCatSheafOf R) ⊤
    ((moduleSheafHomFunctor F).obj M) ((moduleSheafHomFunctor F').obj M')
    (homEquivStructureHom F M f) (moduleSheafHomMap h g)
  refine Eq.trans ?_ hn.symm
  rw [moduleSectionsAddEquiv_homEquivStructureHom, moduleSectionsAddEquiv_homEquivStructureHom]
  apply (moduleSheafHomGlobalSectionsAddEquiv F' M').injective
  rw [AddEquiv.apply_symm_apply]
  refine Eq.trans ?_ (moduleSheafHom_global_map h g _).symm
  change h ≫ f ≫ g = h ≫ moduleSheafHomGlobalSectionsAddEquiv F M
    ((moduleSheafHomGlobalSectionsAddEquiv F M).symm f) ≫ g
  rw [AddEquiv.apply_symm_apply]

/-- Naturality of `Hom(F, M) ≅ Hom(𝒪_X, ℋom(F, M))` in `M`. -/
lemma homEquivStructureHom_comp (F : 𝓜) {M M' : 𝓜} (f : F ⟶ M) (g : M ⟶ M') :
    homEquivStructureHom F M' (f ≫ g) =
      homEquivStructureHom F M f ≫ (moduleSheafHomFunctor F).map g := by
  have h := homEquivStructureHom_naturality (𝟙 F) f g
  rw [Category.id_comp] at h
  exact h

/-- Naturality of `Hom(F, M) ≅ Hom(𝒪_X, ℋom(F, M))` in `F`. -/
lemma homEquivStructureHom_precomp {F F' : 𝓜} (h : F' ⟶ F) {M : 𝓜} (f : F ⟶ M) :
    homEquivStructureHom F' M (h ≫ f) =
      homEquivStructureHom F M f ≫ (moduleSheafHomPrecomp h).app M := by
  have h' := homEquivStructureHom_naturality h f (𝟙 M)
  rw [Category.comp_id] at h'
  exact h'

private theorem rightDerived_eq_sheafExt (F : 𝓜) (n : ℕ) :
    ((moduleSheafHomBifunctor R).obj (op F)).rightDerived n = sheafExt F n :=
  rfl

section

variable (F : 𝓜) {G : 𝓜} (I : InjectiveResolution G) (n : ℕ)

/-- The morphism `𝒪_X ⟶ ℰxtⁿ(F, G)` (a global section of `ℰxtⁿ(F, G)`) defined by a cocycle
`f : F ⟶ Iⁿ` of the global-Hom complex `Hom(F, I^•)`: viewed as a global cocycle of the sheaf-Hom
complex `ℋom(F, I^•)` through `Hom(F, Iⁿ) ≅ Hom(𝒪_X, ℋom(F, Iⁿ))`, it defines a global section of
the cohomology sheaf `ℋⁿ(ℋom(F, I^•)) ≅ ℰxtⁿ(F, G)`. -/
noncomputable def cocycleSheafExtClass (f : F ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) : 𝒪ₓ ⟶ (sheafExt F n).obj G :=
  ExtToDerived.cocycleClass ((moduleSheafHomBifunctor R).obj (op F)) (homEquivStructureHom F)
    (homEquivStructureHom_comp F) I n (sheafExt F n) (rightDerived_eq_sheafExt F n) f hf

variable [HasExt.{w} 𝓜]

/-- **The global-to-sheaf Ext map, computed from an injective resolution.** For an injective
resolution `G ⟶ I^•`, the additive map `Extⁿ(F, G) ⟶ Γ(X, ℰxtⁿ(F, G))` sending the class of a
cocycle `f : F ⟶ Iⁿ` of `Hom(F, I^•)` to the class of the corresponding global cocycle of
`ℋom(F, I^•)` in `Γ(X, ℋⁿ(ℋom(F, I^•))) ≅ Γ(X, ℰxtⁿ(F, G))`. -/
noncomputable def globalToSheafExtOf :
    Ext.{w} F G n →+ ((sheafExt F n).obj G).val.obj (op ⊤) :=
  (moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((sheafExt F n).obj G)).toAddMonoidHom.comp
    (ExtToDerived.toDerived ((moduleSheafHomBifunctor R).obj (op F)) (homEquivStructureHom F)
      (homEquivStructureHom_comp F) I n (sheafExt F n) (rightDerived_eq_sheafExt F n))

variable {F I n}

/-- On the class of a cocycle `f : F ⟶ Iⁿ`, the map computed from the resolution `I` is the global
section defined by `f` as a global cocycle of `ℋom(F, I^•)`. -/
lemma globalToSheafExtOf_extMk (f : F ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    globalToSheafExtOf F I n (I.extMk f (n + 1) rfl hf) =
      moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ _ (cocycleSheafExtClass F I n f hf) :=
  congrArg (moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((sheafExt F n).obj G))
    (ExtToDerived.toDerived_extMk ((moduleSheafHomBifunctor R).obj (op F)) (homEquivStructureHom F)
      (homEquivStructureHom_comp F) (sheafExt F n) (rightDerived_eq_sheafExt F n) f hf)

/-- The map computed from an injective resolution does not depend on the resolution. -/
lemma globalToSheafExtOf_eq (I' : InjectiveResolution G) :
    globalToSheafExtOf F I n = globalToSheafExtOf F I' n := by
  rw [globalToSheafExtOf, globalToSheafExtOf,
    ExtToDerived.toDerived_eq ((moduleSheafHomBifunctor R).obj (op F)) (homEquivStructureHom F)
      (homEquivStructureHom_comp F) (sheafExt F n) (rightDerived_eq_sheafExt F n) I']

end

variable [HasExt.{w} 𝓜]

variable (F G : 𝓜) (n : ℕ) in
/-- **The global-to-sheaf Ext map**, the natural map of Hartshorne III.6, Proposition 6.9
(p. 236). For `𝒪_X`-modules `F` and `G`, the additive map `Extⁿ(F, G) ⟶ Γ(X, ℰxtⁿ(F, G))`,
computed from an injective resolution `G ⟶ I^•`: the class of a cocycle `f : F ⟶ Iⁿ` of the
global-Hom complex `Hom(F, I^•)` is sent to the class of the corresponding global cocycle of the
sheaf-Hom complex `ℋom(F, I^•)` in `Γ(X, ℋⁿ(ℋom(F, I^•))) ≅ Γ(X, ℰxtⁿ(F, G))`. It is defined with
Mathlib's chosen resolution and does not depend on it
(`Hartshorne.Ringed.globalToSheafExt_extMk`). -/
noncomputable def globalToSheafExt : Ext.{w} F G n →+ ((sheafExt F n).obj G).val.obj (op ⊤) :=
  globalToSheafExtOf F (injectiveResolution G) n

private lemma globalToSheafExt_apply (F G : 𝓜) (n : ℕ) (x : Ext.{w} F G n) :
    globalToSheafExt F G n x = moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((sheafExt F n).obj G)
      (ExtToDerived.toDerived ((moduleSheafHomBifunctor R).obj (op F)) (homEquivStructureHom F)
        (homEquivStructureHom_comp F) (injectiveResolution G) n (sheafExt F n)
        (rightDerived_eq_sheafExt F n) x) :=
  rfl

/-- **The global-to-sheaf Ext map from any injective resolution.** For an injective resolution
`G ⟶ I^•` and a cocycle `f : F ⟶ Iⁿ` of the global-Hom complex `Hom(F, I^•)`, the image of its
class in `Extⁿ(F, G)` is the global section of `ℰxtⁿ(F, G) ≅ ℋⁿ(ℋom(F, I^•))` given by `f` viewed
as a global cocycle of the sheaf-Hom complex `ℋom(F, I^•)`. -/
theorem globalToSheafExt_extMk {F G : 𝓜} {n : ℕ} (I : InjectiveResolution G)
    (f : F ⟶ I.cocomplex.X n) (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    globalToSheafExt F G n (I.extMk f (n + 1) rfl hf) =
      moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ _ (cocycleSheafExtClass F I n f hf) := by
  rw [globalToSheafExt, globalToSheafExtOf_eq (I := injectiveResolution G) I,
    globalToSheafExtOf_extMk]

/-- **The global-to-sheaf Ext map in degree zero.** For `g : F ⟶ G`, the image of the class of
`g` in `Ext⁰(F, G)` is the global section of `ℰxt⁰(F, G)` corresponding to `g` under the
identifications `Hom(F, G) ≅ Γ(X, ℋom(F, G))` and `ℋom(F, G) ≅ ℰxt⁰(F, G)`. -/
theorem globalToSheafExt_mk₀ {F G : 𝓜} (g : F ⟶ G) :
    globalToSheafExt F G 0 (Ext.mk₀ g) =
      ((moduleSheafHomFunctor F).rightDerivedZeroIsoSelf.inv.app G).val.app (op ⊤)
        ((moduleSheafHomGlobalSectionsAddEquiv F G).symm g) := by
  have h := congrArg (moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((sheafExt F 0).obj G))
    (ExtToDerived.toDerived_mk₀ ((moduleSheafHomBifunctor R).obj (op F)) (homEquivStructureHom F)
      (homEquivStructureHom_comp F) (I := injectiveResolution G) (sheafExt F 0)
      (rightDerived_eq_sheafExt F 0) g)
  refine h.trans ?_
  rw [moduleSectionsAddEquiv_naturality]
  erw [moduleSectionsAddEquiv_homEquivStructureHom]
  rfl

/-- **Naturality of the global-to-sheaf Ext map in the second variable.** For `g : G ⟶ G'`, the
square formed with `Extⁿ(F, g)` and `Γ(X, ℰxtⁿ(F, g))` commutes. -/
theorem globalToSheafExt_comp_mk₀ {F G G' : 𝓜} {n : ℕ} (g : G ⟶ G') (e : Ext.{w} F G n) :
    globalToSheafExt F G' n (e.comp (Ext.mk₀ g) (add_zero n)) =
      ((sheafExt F n).map g).val.app (op ⊤) (globalToSheafExt F G n e) := by
  have h := congrArg (moduleSectionsAddEquiv (ringCatSheafOf R) ⊤ ((sheafExt F n).obj G'))
    (ExtToDerived.toDerived_comp_mk₀ ((moduleSheafHomBifunctor R).obj (op F))
      (homEquivStructureHom F)
      (homEquivStructureHom_comp F) (sheafExt F n) (rightDerived_eq_sheafExt F n)
      (I := injectiveResolution G) g (injectiveResolution G') e)
  refine h.trans ?_
  rw [moduleSectionsAddEquiv_naturality]
  rfl

omit [HasExt.{w} 𝓜] in
private lemma extMap_eq_sheafExtPrecomp {F F' : 𝓜} (h : F' ⟶ F) (G : 𝓜) (n : ℕ) :
    SheafExtContravariant.extMap (moduleSheafHomBifunctor R) sheafExt rightDerived_eq_sheafExt h
      G n = sheafExtPrecomp h G n :=
  rfl

/-- **Naturality of the global-to-sheaf Ext map in the first variable.** For `h : F' ⟶ F`, the
square formed with `Extⁿ(h, G)` and `Γ(X, ℰxtⁿ(h, G))` commutes. -/
theorem globalToSheafExt_mk₀_comp {F F' G : 𝓜} {n : ℕ} (h : F' ⟶ F) (e : Ext.{w} F G n) :
    globalToSheafExt F' G n ((Ext.mk₀ h).comp e (zero_add n)) =
      (sheafExtPrecomp h G n).val.app (op ⊤) (globalToSheafExt F G n e) := by
  rw [globalToSheafExt_apply, globalToSheafExt_apply, ← extMap_eq_sheafExtPrecomp,
    ExtToDerived.toDerived_mk₀_comp_extMap (moduleSheafHomBifunctor R) sheafExt
      rightDerived_eq_sheafExt homEquivStructureHom homEquivStructureHom_comp
      (fun h f ↦ homEquivStructureHom_precomp h f) h n e,
    moduleSectionsAddEquiv_naturality]

end Ringed

end Hartshorne
