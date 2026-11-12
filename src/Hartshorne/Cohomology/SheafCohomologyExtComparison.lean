/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SheafCohomology
import Hartshorne.Cohomology.RightDerivedLongExactSequence
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Sheaf cohomology as Ext from the constant sheaf

For a topological space `X`, Hartshorne's sheaf cohomology `H^n(X,-) = R^nΓ(X,-)`
(`Hartshorne.sheafCohomology`) is isomorphic to `Ext^n(ℤ_X,-)` in the category of abelian
sheaves on `X`, which is Mathlib's `CategoryTheory.Sheaf.functorH`
(`Hartshorne.sheafCohomologyIsoExt`). The isomorphism is natural in the sheaf, is the
canonical identification `H^0(X,F) ≅ Γ(X,F) ≅ Hom(ℤ_X,F) = Ext^0(ℤ_X,F)` in degree zero
(`Hartshorne.sheafCohomologyIsoExt_zero`), and carries the connecting homomorphisms of
sheaf cohomology to those of Ext, i.e. to the Yoneda product with the class of the short exact
sequence (`Hartshorne.sheafCohomologyIsoExt_δ`).

## Construction

Evaluation at the global section `1` of `ℤ_X` is a natural isomorphism
`Hom(ℤ_X,-) ≅ Γ(X,-)` (`Hartshorne.coyonedaZIsoSections`). Applied termwise to an injective
resolution `F ⟶ I•`, it identifies the complexes `Γ(X,I•)` and `Hom(ℤ_X,I•)`, whose cohomology
groups are `H^n(X,F)` and `R^n Hom(ℤ_X,-)(F)`; this gives
`H^n(X,-) ≅ R^n Hom(ℤ_X,-)` (`Hartshorne.sheafCohomologyIsoRightDerivedHom`). Since the
connecting maps of right derived functors are computed on horseshoe resolutions, and the
termwise isomorphism is a morphism between the resulting short exact sequences of complexes, it
commutes with the connecting maps (`Hartshorne.rightDerivedδ_natTrans`). Hartshorne III.6
(p. 233) defines `Ext^n(F,-)` as `R^n Hom(F,-)`, so this is the comparison of the book.

It remains to identify `R^n Hom(A,-)` with Mathlib's `Ext^n(A,-)`, defined through the derived
category, compatibly with connecting maps. Both are effaceable cohomological functors on a
category with enough injectives: they have long exact sequences, natural connecting maps, and
vanish on injective objects in positive degrees. For such families `T₁`, `T₂` and an
isomorphism `e₀ : T₁⁰ ≅ T₂⁰`, embedding `A` into an injective `I` with cokernel `Q` presents
`T^{n+1}(A)` as the cokernel of `T^n(I) ⟶ T^n(Q)` via the connecting map, so `e_n` at `Q`
descends to `e_{n+1}` at `A` (`Hartshorne.EffaceableCohomologicalFunctor.compIso`). Naturality
and compatibility with the connecting maps of every short exact sequence follow from
naturality of the connecting maps, by mapping a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` to
`0 ⟶ A ⟶ I ⟶ Q ⟶ 0` (`Hartshorne.rightDerivedCoyonedaIsoExt`).
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v u

namespace Hartshorne

/-- A family of functors `T^n : C ⥤ D` with connecting maps for short exact sequences, natural
and giving exact sequences `T^n(B) ⟶ T^n(C) ⟶ T^{n+1}(A) ⟶ T^{n+1}(B)`, and vanishing on
injective objects in positive degrees. -/
structure EffaceableCohomologicalFunctor (C : Type u) [Category.{v} C] [Abelian C]
    (D : Type*) [Category* D] [Abelian D] where
  /-- The functors. -/
  F : ℕ → C ⥤ D
  /-- The connecting maps. -/
  δ : ∀ {S : ShortComplex C}, S.ShortExact → ∀ n : ℕ, (F n).obj S.X₃ ⟶ (F (n + 1)).obj S.X₁
  map_g_comp_δ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ),
    (F n).map S.g ≫ δ hS n = 0
  δ_comp_map_f : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ),
    δ hS n ≫ (F (n + 1)).map S.f = 0
  exact₃ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk _ _ (map_g_comp_δ hS n)).Exact
  exact₁ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk _ _ (δ_comp_map_f hS n)).Exact
  naturality : ∀ {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (n : ℕ),
    δ hS₁ n ≫ (F (n + 1)).map φ.τ₁ = (F n).map φ.τ₃ ≫ δ hS₂ n
  isZero_injective : ∀ (I : C) [Injective I] (n : ℕ), IsZero ((F (n + 1)).obj I)

namespace EffaceableCohomologicalFunctor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type*} [Category* D] [Abelian D]

/-- The short exact sequence `0 ⟶ A ⟶ I(A) ⟶ I(A)/A ⟶ 0` for the chosen injective `I(A)`. -/
noncomputable abbrev injSC (A : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A)) (cokernel.condition _)

lemma injSC_shortExact (A : C) : (injSC A).ShortExact :=
  ShortComplex.ShortExact.mk' ((injSC A).exact_of_g_is_cokernel (cokernelIsCokernel _))
    (inferInstanceAs (Mono (Injective.ι A))) (inferInstanceAs (Epi (cokernel.π _)))

variable (T : EffaceableCohomologicalFunctor C D)

lemma epi_δ_injSC (A : C) (n : ℕ) : Epi (T.δ (injSC_shortExact A) n) :=
  (T.exact₁ (injSC_shortExact A) n).epi_f
    ((T.isZero_injective (Injective.under A) n).eq_of_tgt _ _)

/-- `T^{n+1}(A)` is the cokernel of `T^n(I(A)) ⟶ T^n(I(A)/A)`, via the connecting map. -/
noncomputable def isColimitInjSC (A : C) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (T.δ (injSC_shortExact A) n)
      (T.map_g_comp_δ (injSC_shortExact A) n)) :=
  have := T.epi_δ_injSC A n
  (T.exact₃ (injSC_shortExact A) n).gIsCokernel

variable (T₁ T₂ : EffaceableCohomologicalFunctor C D)

/-- One step of the comparison: from `T₁^n ≅ T₂^n` to the component of `T₁^{n+1} ≅ T₂^{n+1}`
at `A`. -/
noncomputable def succApp {n : ℕ} (e : T₁.F n ≅ T₂.F n) (A : C) :
    (T₁.F (n + 1)).obj A ≅ (T₂.F (n + 1)).obj A where
  hom := (CokernelCofork.IsColimit.desc' (T₁.isColimitInjSC A n)
    (e.hom.app _ ≫ T₂.δ (injSC_shortExact A) n) (by
      rw [e.hom.naturality_assoc, T₂.map_g_comp_δ, comp_zero])).1
  inv := (CokernelCofork.IsColimit.desc' (T₂.isColimitInjSC A n)
    (e.inv.app _ ≫ T₁.δ (injSC_shortExact A) n) (by
      rw [e.inv.naturality_assoc, T₁.map_g_comp_δ, comp_zero])).1
  hom_inv_id := by
    have := T₁.epi_δ_injSC A n
    rw [← cancel_epi (T₁.δ (injSC_shortExact A) n), Category.comp_id]
    erw [reassoc_of% (CokernelCofork.IsColimit.desc' (T₁.isColimitInjSC A n) _ _).2]
    rw [Category.assoc]
    erw [(CokernelCofork.IsColimit.desc' (T₂.isColimitInjSC A n) _ _).2]
    simp
  inv_hom_id := by
    have := T₂.epi_δ_injSC A n
    rw [← cancel_epi (T₂.δ (injSC_shortExact A) n), Category.comp_id]
    erw [reassoc_of% (CokernelCofork.IsColimit.desc' (T₂.isColimitInjSC A n) _ _).2]
    rw [Category.assoc]
    erw [(CokernelCofork.IsColimit.desc' (T₁.isColimitInjSC A n) _ _).2]
    simp

lemma δ_succApp_hom {n : ℕ} (e : T₁.F n ≅ T₂.F n) (A : C) :
    T₁.δ (injSC_shortExact A) n ≫ (succApp T₁ T₂ e A).hom =
      e.hom.app _ ≫ T₂.δ (injSC_shortExact A) n :=
  (CokernelCofork.IsColimit.desc' (T₁.isColimitInjSC A n) _ _).2

/-- A morphism `f : A ⟶ B` extends to a morphism of the chosen injective short exact
sequences. -/
noncomputable def injSCMap {A B : C} (f : A ⟶ B) : injSC A ⟶ injSC B where
  τ₁ := f
  τ₂ := Injective.factorThru (f ≫ Injective.ι B) (Injective.ι A)
  τ₃ := cokernel.desc _ (Injective.factorThru (f ≫ Injective.ι B) (Injective.ι A) ≫
    cokernel.π _) (by simp)
  comm₁₂ := by simp
  comm₂₃ := by simp

/-- A short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` maps to the chosen injective short exact
sequence of `A`, by the identity on `A`. -/
noncomputable def toInjSC {S : ShortComplex C} (hS : S.ShortExact) : S ⟶ injSC S.X₁ :=
  have := hS.mono_f
  { τ₁ := 𝟙 _
    τ₂ := Injective.factorThru (Injective.ι S.X₁) S.f
    τ₃ := hS.gIsCokernel.desc (CokernelCofork.ofπ
      (Injective.factorThru (Injective.ι S.X₁) S.f ≫ cokernel.π _) (by simp))
    comm₁₂ := by simp
    comm₂₃ := by
      have := hS.gIsCokernel.fac (CokernelCofork.ofπ
        (Injective.factorThru (Injective.ι S.X₁) S.f ≫ cokernel.π (Injective.ι S.X₁))
        (by simp)) WalkingParallelPair.one
      simpa using this.symm }

/-- The comparison isomorphisms `T₁^n ≅ T₂^n` extending `e₀ : T₁^0 ≅ T₂^0`. -/
noncomputable def compIso (e₀ : T₁.F 0 ≅ T₂.F 0) : ∀ n : ℕ, T₁.F n ≅ T₂.F n
  | 0 => e₀
  | n + 1 => NatIso.ofComponents (fun A => succApp T₁ T₂ (compIso e₀ n) A) (by
      intro A B f
      have := T₁.epi_δ_injSC A n
      rw [← cancel_epi (T₁.δ (injSC_shortExact A) n)]
      have h₁ := T₁.naturality (injSCMap f) (injSC_shortExact A) (injSC_shortExact B) n
      dsimp only [injSCMap] at h₁
      have h₂ := T₂.naturality (injSCMap f) (injSC_shortExact A) (injSC_shortExact B) n
      dsimp only [injSCMap] at h₂
      rw [reassoc_of% h₁, δ_succApp_hom, reassoc_of% (δ_succApp_hom T₁ T₂ (compIso e₀ n) A), h₂,
        NatTrans.naturality_assoc])

@[simp]
lemma compIso_zero (e₀ : T₁.F 0 ≅ T₂.F 0) : compIso T₁ T₂ e₀ 0 = e₀ := rfl

/-- The comparison isomorphisms commute with the connecting maps. -/
theorem δ_compIso_hom (e₀ : T₁.F 0 ≅ T₂.F 0) {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) :
    T₁.δ hS n ≫ (compIso T₁ T₂ e₀ (n + 1)).hom.app S.X₁ =
      (compIso T₁ T₂ e₀ n).hom.app S.X₃ ≫ T₂.δ hS n := by
  have h₁ := T₁.naturality (toInjSC hS) hS (injSC_shortExact S.X₁) n
  have h₂ := T₂.naturality (toInjSC hS) hS (injSC_shortExact S.X₁) n
  dsimp only [toInjSC] at h₁ h₂
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h₁ h₂
  rw [h₁, h₂]
  change _ ≫ (succApp T₁ T₂ (compIso T₁ T₂ e₀ n) S.X₁).hom = _
  rw [Category.assoc, δ_succApp_hom, NatTrans.naturality_assoc]

end EffaceableCohomologicalFunctor

section RightDerived

open RightDerivedLES

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D]

/-- The right derived functors of an additive functor, with the connecting maps of
`Hartshorne.rightDerivedδ`, as an effaceable cohomological functor. -/
noncomputable def rightDerivedEffaceable (G : C ⥤ D) [G.Additive] :
    EffaceableCohomologicalFunctor C D where
  F n := G.rightDerived n
  δ hS n := rightDerivedδ G hS n
  map_g_comp_δ hS n := Horseshoe.map_g_comp_δ _ hS _ _ n
  δ_comp_map_f hS n := Horseshoe.δ_comp_map_f _ hS _ _ n
  exact₃ hS n := rightDerived_exact₃ _ hS n
  exact₁ hS n := rightDerived_exact₁ _ hS n
  naturality φ hS₁ hS₂ n := rightDerivedδ_naturality _ φ hS₁ hS₂ n
  isZero_injective I _ n := Functor.isZero_rightDerived_obj_injective_succ _ n I

/-- A natural isomorphism `F ≅ G` of additive functors induces `RⁿF ≅ RⁿG`. On an injective
resolution `I` it is the isomorphism of complexes `F(I) ≅ G(I)` applied termwise, followed by
cohomology (`CategoryTheory.InjectiveResolution.rightDerived_app_eq`). -/
@[simps]
noncomputable def rightDerivedIsoOfIso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- On the horseshoe resolution built on injective resolutions `I₁` and `I₃` of the ends of a
short exact sequence, `α : F ⟶ G` applied termwise is a morphism from the short exact sequence
of complexes obtained by applying `F` to the one obtained by applying `G`; hence the morphism
`RⁿF ⟶ RⁿG` induced by `α` commutes with the connecting maps. -/
theorem horseshoeδ_natTrans {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    {S : ShortComplex C} (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) (n : ℕ) :
    Horseshoe.δ F hS I₁ I₃ n ≫ (NatTrans.rightDerived α (n + 1)).app S.X₁ =
      (NatTrans.rightDerived α n).app S.X₃ ≫ Horseshoe.δ G hS I₁ I₃ n := by
  let ψ : Horseshoe.shortComplexMap hS I₁ I₃ F ⟶ Horseshoe.shortComplexMap hS I₁ I₃ G :=
    { τ₁ := (NatTrans.mapHomologicalComplex α _).app _
      τ₂ := (NatTrans.mapHomologicalComplex α _).app _
      τ₃ := (NatTrans.mapHomologicalComplex α _).app _
      comm₁₂ := ((NatTrans.mapHomologicalComplex α _).naturality _).symm
      comm₂₃ := ((NatTrans.mapHomologicalComplex α _).naturality _).symm }
  have hnat := HomologicalComplex.HomologySequence.δ_naturality ψ
    (Horseshoe.shortExact_map hS I₁ I₃ F) (Horseshoe.shortExact_map hS I₁ I₃ G) n (n + 1)
    (upRel n)
  have e₁ : (NatTrans.rightDerived α (n + 1)).app S.X₁ = (isoH F I₁ (n + 1)).hom ≫
      HomologicalComplex.homologyMap ψ.τ₁ (n + 1) ≫ (isoH G I₁ (n + 1)).inv :=
    InjectiveResolution.rightDerived_app_eq α I₁ (n + 1)
  have e₃ : (NatTrans.rightDerived α n).app S.X₃ = (isoH F I₃ n).hom ≫
      HomologicalComplex.homologyMap ψ.τ₃ n ≫ (isoH G I₃ n).inv :=
    InjectiveResolution.rightDerived_app_eq α I₃ n
  rw [e₁, e₃]
  simp only [Horseshoe.δ, Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hnat]

/-- The morphism `RⁿF ⟶ RⁿG` induced by `α : F ⟶ G` commutes with the connecting maps. -/
theorem rightDerivedδ_natTrans {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    rightDerivedδ F hS n ≫ (NatTrans.rightDerived α (n + 1)).app S.X₁ =
      (NatTrans.rightDerived α n).app S.X₃ ≫ rightDerivedδ G hS n :=
  horseshoeδ_natTrans α hS _ _ n

/-- The canonical map `F ⟶ R⁰F` is natural in the additive functor `F`. -/
theorem toRightDerivedZero_natTrans {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    α ≫ G.toRightDerivedZero = F.toRightDerivedZero ≫ NatTrans.rightDerived α 0 := by
  ext A
  let I := injectiveResolution A
  let φ := (NatTrans.mapHomologicalComplex α _).app I.cocomplex
  have eF : F.toRightDerivedZero.app A = I.toRightDerivedZero' F ≫
      (CochainComplex.isoHomologyπ₀ _).hom ≫ (isoH F I 0).inv :=
    I.toRightDerivedZero_eq F
  have eG : G.toRightDerivedZero.app A = I.toRightDerivedZero' G ≫
      (CochainComplex.isoHomologyπ₀ _).hom ≫ (isoH G I 0).inv :=
    I.toRightDerivedZero_eq G
  have eα : (NatTrans.rightDerived α 0).app A =
      (isoH F I 0).hom ≫ HomologicalComplex.homologyMap φ 0 ≫ (isoH G I 0).inv :=
    I.rightDerived_app_eq α 0
  have k₁ : α.app A ≫ I.toRightDerivedZero' G =
      I.toRightDerivedZero' F ≫ HomologicalComplex.cyclesMap φ 0 := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ _), Category.assoc, Category.assoc,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles, HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    exact (α.naturality _).symm
  rw [NatTrans.comp_app, NatTrans.comp_app, eF, eG, eα]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, HomologicalComplex.isoHomologyπ_hom]
  rw [reassoc_of% k₁, HomologicalComplex.homologyπ_naturality_assoc]

/-- For left exact `F` and `G`, the identifications `R⁰F ≅ F` and `R⁰G ≅ G` carry the map
`R⁰F ⟶ R⁰G` induced by `α : F ⟶ G` to `α`. -/
theorem rightDerived_zero_comp_rightDerivedZeroIsoSelf_hom {F G : C ⥤ D} [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G] (α : F ⟶ G) :
    NatTrans.rightDerived α 0 ≫ G.rightDerivedZeroIsoSelf.hom =
      F.rightDerivedZeroIsoSelf.hom ≫ α := by
  rw [← cancel_epi F.toRightDerivedZero, ← Category.assoc, ← toRightDerivedZero_natTrans,
    Category.assoc, Functor.rightDerivedZeroIsoSelf_inv_hom_id, Category.comp_id,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_assoc]

end RightDerived

section Ext

open Abelian EffaceableCohomologicalFunctor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

/-- `Ext^n(A,-)`, with the connecting maps given by the Yoneda product with the classes of short
exact sequences, as an effaceable cohomological functor. -/
noncomputable def extEffaceable (A : C) : EffaceableCohomologicalFunctor C AddCommGrpCat.{v} where
  F n := extFunctorObj.{v} A n
  δ hS n := AddCommGrpCat.ofHom (hS.extClass.{v}.postcomp A rfl)
  map_g_comp_δ {S} hS n := by
    refine AddCommGrpCat.ext fun (x : Ext.{v} A S.X₂ n) => ?_
    change (x.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass.{v} rfl = 0
    simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
      Ext.comp_zero]
  δ_comp_map_f {S} hS n := by
    refine AddCommGrpCat.ext fun (x : Ext.{v} A S.X₃ n) => ?_
    change (x.comp hS.extClass.{v} rfl).comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0
    simp only [Ext.comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp,
      Ext.comp_zero]
  exact₃ hS n := Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl
  exact₁ hS n := Ext.covariant_sequence_exact₁' A hS n (n + 1) rfl
  naturality {S₁ S₂} φ hS₁ hS₂ n := by
    refine AddCommGrpCat.ext fun (x : Ext.{v} A S₁.X₃ n) => ?_
    change (x.comp hS₁.extClass.{v} rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
      (x.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hS₂.extClass.{v} rfl
    rw [Ext.comp_assoc_of_third_deg_zero, hS₁.extClass_naturality hS₂ φ,
      Ext.comp_assoc_of_second_deg_zero]
  isZero_injective I _ n := by
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact Ext.subsingleton_of_injective _ _ n

/-- `Hom(A,-) ≅ Ext^0(A,-)`, naturally. -/
noncomputable def coyonedaIsoExtZero (A : C) :
    preadditiveCoyoneda.obj (op A) ≅ extFunctorObj.{v} A 0 :=
  NatIso.ofComponents (fun B => (Ext.addEquiv₀ (X := A) (Y := B)).symm.toAddCommGrpIso)
    (fun {B B'} f => by
      ext g
      exact (Ext.mk₀_comp_mk₀ g f).symm)

variable [EnoughInjectives C]

/-- `R^n Hom(A,-) ≅ Ext^n(A,-)`, extending `R⁰Hom(A,-) ≅ Hom(A,-) ≅ Ext^0(A,-)` compatibly with
the connecting maps (`Hartshorne.EffaceableCohomologicalFunctor.compIso`). -/
noncomputable def rightDerivedCoyonedaIsoExt (A : C) (n : ℕ) :
    (preadditiveCoyoneda.obj (op A)).rightDerived n ≅ extFunctorObj.{v} A n :=
  compIso (rightDerivedEffaceable (preadditiveCoyoneda.obj (op A))) (extEffaceable A)
    ((preadditiveCoyoneda.obj (op A)).rightDerivedZeroIsoSelf ≪≫ coyonedaIsoExtZero A) n

/-- The isomorphisms `R^n Hom(A,-) ≅ Ext^n(A,-)` carry the connecting maps of right derived
functors to the Yoneda product with the class of the short exact sequence. -/
theorem rightDerivedCoyonedaIsoExt_δ (A : C) {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) :
    rightDerivedδ (preadditiveCoyoneda.obj (op A)) hS n ≫
        (rightDerivedCoyonedaIsoExt A (n + 1)).hom.app S.X₁ =
      (rightDerivedCoyonedaIsoExt A n).hom.app S.X₃ ≫
        AddCommGrpCat.ofHom (hS.extClass.{v}.postcomp A rfl) :=
  δ_compIso_hom (rightDerivedEffaceable _) (extEffaceable A) _ hS n

end Ext

section Sheaf

open Abelian

variable (X : TopCat.{u})

/-- The constant sheaf `ℤ_X` (the sheafification of the constant presheaf with value `ℤ`, here
`ULift ℤ`), as an abelian sheaf on `X`. -/
noncomputable abbrev constantSheafZ : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- The global section `1` of the constant sheaf `ℤ_X`. -/
noncomputable def constantSheafZOne : (constantSheafZ X).obj.obj (op ⊤) :=
  (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (isTerminalTop (α := Opens X))).unit.app (AddCommGrpCat.of (ULift ℤ)) (ULift.up 1)

/-- Evaluation of a morphism `ℤ_X ⟶ F` at the global section `1`. -/
noncomputable def constantSheafZEvalOne (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (constantSheafZ X ⟶ F) →+ F.obj.obj (op ⊤) where
  toFun f := f.hom.app (op ⊤) (constantSheafZOne X)
  map_zero' := rfl
  map_add' _ _ := rfl

lemma constantSheafZEvalOne_bijective (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Bijective (constantSheafZEvalOne X F) := by
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (isTerminalTop (α := Opens X))
  have key : ∀ G : AddCommGrpCat.{u},
      Function.Bijective (fun g : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G => g (ULift.up 1)) :=
    fun G => by
      let e : (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G) ≃ G :=
        ConcreteCategory.homEquiv.trans (uliftZMultiplesHom G).symm
      exact e.bijective
  have h : ⇑(constantSheafZEvalOne X F) = (fun g => g (ULift.up 1)) ∘ adj.homEquiv _ F := by
    funext f
    rfl
  rw [h]
  exact (key _).comp (adj.homEquiv _ F).bijective

/-- `Hom(ℤ_X,-) ≅ Γ(X,-)`, naturally, by evaluation at the global section `1` of `ℤ_X`. -/
noncomputable def coyonedaZIsoSections :
    preadditiveCoyoneda.obj (op (constantSheafZ X)) ≅ sheafSectionsOver (X := X) ⊤ :=
  NatIso.ofComponents
    (fun F => (AddEquiv.ofBijective _ (constantSheafZEvalOne_bijective X F)).toAddCommGrpIso)
    (fun {F G} f => by
      ext g
      rfl)

/-- `H^n(X,-) ≅ R^n Hom(ℤ_X,-)`: on an injective resolution `F ⟶ I•`, the isomorphism
`Γ(X,-) ≅ Hom(ℤ_X,-)` applied termwise identifies the complexes `Γ(X,I•)` and `Hom(ℤ_X,I•)`. -/
noncomputable def sheafCohomologyIsoRightDerivedHom (n : ℕ) :
    sheafCohomology X n ≅ (preadditiveCoyoneda.obj (op (constantSheafZ X))).rightDerived n :=
  rightDerivedIsoOfIso (coyonedaZIsoSections X).symm n

/-- **Sheaf cohomology as Ext from the constant sheaf.** For a topological space `X` and
`n : ℕ`, an isomorphism `H^n(X,F) ≅ Ext^n(ℤ_X,F)` natural in the abelian sheaf `F`, where
`H^n(X,-) = R^nΓ(X,-)` is Hartshorne's sheaf cohomology and `Ext^n(ℤ_X,F)` is the Ext group of
the abelian category of abelian sheaves on `X` (Mathlib's `Abelian.Ext`; the same groups as
`CategoryTheory.Sheaf.H F n`). It is the canonical identification in degree zero
(`Hartshorne.sheafCohomologyIsoExt_zero`) and commutes with the connecting homomorphisms
(`Hartshorne.sheafCohomologyIsoExt_δ`). -/
noncomputable def sheafCohomologyIsoExt (n : ℕ) :
    sheafCohomology X n ≅ extFunctorObj.{u} (constantSheafZ X) n :=
  sheafCohomologyIsoRightDerivedHom X n ≪≫ rightDerivedCoyonedaIsoExt (constantSheafZ X) n

/-- In degree zero, `H^0(X,F) ≅ Ext^0(ℤ_X,F) = Hom(ℤ_X,F)` followed by evaluation at the global
section `1` of `ℤ_X` is the identification `H^0(X,F) ≅ Γ(X,F)`. -/
theorem sheafCohomologyIsoExt_zero (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : (sheafCohomology X 0).obj F) :
    (Ext.addEquiv₀ ((sheafCohomologyIsoExt X 0).hom.app F x)).hom.app (op ⊤)
        (constantSheafZOne X) =
      (sheafCohomologyZeroIso X).hom.app F x := by
  have h := rightDerived_zero_comp_rightDerivedZeroIsoSelf_hom (coyonedaZIsoSections X).inv
  have hx := ConcreteCategory.congr_hom (congrArg (fun φ => φ.app F) h) x
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hx
  change constantSheafZEvalOne X F (Ext.addEquiv₀ (Ext.addEquiv₀.symm
    ((preadditiveCoyoneda.obj (op (constantSheafZ X))).rightDerivedZeroIsoSelf.hom.app F
      ((NatTrans.rightDerived (coyonedaZIsoSections X).inv 0).app F x)))) = _
  erw [AddEquiv.apply_symm_apply]
  rw [hx]
  exact ConcreteCategory.congr_hom ((coyonedaZIsoSections X).inv_hom_id_app F) _

/-- The isomorphisms `H^n(X,-) ≅ Ext^n(ℤ_X,-)` carry the connecting homomorphism
`H^n(X,F'') ⟶ H^{n+1}(X,F')` of a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` to the Yoneda
product `Ext^n(ℤ_X,F'') ⟶ Ext^{n+1}(ℤ_X,F')` with its class in `Ext^1(F'',F')`. -/
theorem sheafCohomologyIsoExt_δ {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ) :
    rightDerivedδ (sheafSectionsOver (X := X) ⊤) hS n ≫
        (sheafCohomologyIsoExt X (n + 1)).hom.app S.X₁ =
      (sheafCohomologyIsoExt X n).hom.app S.X₃ ≫
        AddCommGrpCat.ofHom (hS.extClass.{u}.postcomp (constantSheafZ X) rfl) := by
  simp only [sheafCohomologyIsoExt, sheafCohomologyIsoRightDerivedHom, Iso.trans_hom,
    NatTrans.comp_app, rightDerivedIsoOfIso_hom, Iso.symm_hom]
  rw [reassoc_of% (rightDerivedδ_natTrans (coyonedaZIsoSections X).inv hS n),
    rightDerivedCoyonedaIsoExt_δ]
  exact (Category.assoc _ _ _).symm

end Sheaf

end Hartshorne
