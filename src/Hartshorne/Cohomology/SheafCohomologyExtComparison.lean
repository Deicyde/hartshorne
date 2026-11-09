/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SheafCohomology
import Hartshorne.Cohomology.RightDerivedLongExactSequence
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

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

Both families are effaceable cohomological functors on a category with enough injectives: they
have long exact sequences, natural connecting maps, and vanish on injective objects in positive
degrees. For such families `T₁`, `T₂` and an isomorphism `e₀ : T₁⁰ ≅ T₂⁰`, embedding `A` into
an injective `I` with cokernel `Q` presents `T^{n+1}(A)` as the cokernel of `T^n(I) ⟶ T^n(Q)`
via the connecting map, so `e_n` at `Q` descends to `e_{n+1}` at `A`
(`Hartshorne.EffaceableCohomologicalFunctor.compIso`). Naturality and compatibility with the
connecting maps of every short exact sequence follow from naturality of the connecting maps,
by mapping a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` to `0 ⟶ A ⟶ I ⟶ Q ⟶ 0`.
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

section Sheaf

open Abelian EffaceableCohomologicalFunctor

variable (X : TopCat.{u})

/-- Sheaf cohomology `H^n(X,-) = R^nΓ(X,-)`, with the connecting maps of right derived functors,
as an effaceable cohomological functor. -/
noncomputable def sheafCohomologyEffaceable :
    EffaceableCohomologicalFunctor (TopCat.Sheaf AddCommGrpCat.{u} X) AddCommGrpCat.{u} where
  F n := sheafCohomology X n
  δ hS n := rightDerivedδ (sheafSectionsOver (X := X) ⊤) hS n
  map_g_comp_δ hS n := RightDerivedLES.Horseshoe.map_g_comp_δ _ hS _ _ n
  δ_comp_map_f hS n := RightDerivedLES.Horseshoe.δ_comp_map_f _ hS _ _ n
  exact₃ hS n := rightDerived_exact₃ _ hS n
  exact₁ hS n := rightDerived_exact₁ _ hS n
  naturality φ hS₁ hS₂ n := rightDerivedδ_naturality _ φ hS₁ hS₂ n
  isZero_injective I _ n := Functor.isZero_rightDerived_obj_injective_succ _ n I

/-- The constant sheaf `ℤ_X` (the sheafification of the constant presheaf with value `ℤ`, here
`ULift ℤ`), as an abelian sheaf on `X`. -/
noncomputable abbrev constantSheafZ : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- The global section `1` of the constant sheaf `ℤ_X`. -/
noncomputable def constantSheafZOne : (constantSheafZ X).obj.obj (op ⊤) :=
  (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (isTerminalTop (α := Opens X))).unit.app (AddCommGrpCat.of (ULift ℤ)) (ULift.up 1)

/-- `Ext^n(ℤ_X,-)` on abelian sheaves, with the connecting maps given by the Yoneda product with
the classes of short exact sequences, as an effaceable cohomological functor. -/
noncomputable def extEffaceable :
    EffaceableCohomologicalFunctor (TopCat.Sheaf AddCommGrpCat.{u} X) AddCommGrpCat.{u} where
  F n := extFunctorObj.{u} (constantSheafZ X) n
  δ hS n := AddCommGrpCat.ofHom (hS.extClass.{u}.postcomp (constantSheafZ X) rfl)
  map_g_comp_δ {S} hS n := by
    refine AddCommGrpCat.ext fun (x : Ext.{u} (constantSheafZ X) S.X₂ n) => ?_
    change (x.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass.{u} rfl = 0
    simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
      Ext.comp_zero]
  δ_comp_map_f {S} hS n := by
    refine AddCommGrpCat.ext fun (x : Ext.{u} (constantSheafZ X) S.X₃ n) => ?_
    change (x.comp hS.extClass.{u} rfl).comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0
    simp only [Ext.comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp,
      Ext.comp_zero]
  exact₃ hS n := Ext.covariant_sequence_exact₃' (constantSheafZ X) hS n (n + 1) rfl
  exact₁ hS n := Ext.covariant_sequence_exact₁' (constantSheafZ X) hS n (n + 1) rfl
  naturality {S₁ S₂} φ hS₁ hS₂ n := by
    refine AddCommGrpCat.ext fun (x : Ext.{u} (constantSheafZ X) S₁.X₃ n) => ?_
    change (x.comp hS₁.extClass.{u} rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
      (x.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hS₂.extClass.{u} rfl
    rw [Ext.comp_assoc_of_third_deg_zero, hS₁.extClass_naturality hS₂ φ,
      Ext.comp_assoc_of_second_deg_zero]
  isZero_injective I _ n := by
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact Ext.subsingleton_of_injective _ _ n

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

/-- `Ext^0(ℤ_X,F) = Hom(ℤ_X,F) ≅ Γ(X,F)`, by evaluation at the global section `1`. -/
noncomputable def constantSheafZExt₀Equiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Ext.{u} (constantSheafZ X) F 0 ≃+ F.obj.obj (op ⊤) :=
  Ext.addEquiv₀.trans (AddEquiv.ofBijective _ (constantSheafZEvalOne_bijective X F))

lemma constantSheafZExt₀Equiv_apply (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : Ext.{u} (constantSheafZ X) F 0) :
    constantSheafZExt₀Equiv X F x = (Ext.addEquiv₀ x).hom.app (op ⊤) (constantSheafZOne X) :=
  rfl

lemma constantSheafZ_addEquiv₀_comp_mk₀ {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : Ext.{u} (constantSheafZ X) F 0) :
    Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ x ≫ f := by
  apply (Ext.mk₀_bijective _ G).injective
  simp only [Ext.addEquiv₀, AddEquiv.coe_mk, Ext.mk₀_homEquiv₀_apply, ← Ext.mk₀_comp_mk₀]

/-- `Γ(X,F) ≅ Ext^0(ℤ_X,F)`, inverse to evaluation at the global section `1`, naturally in
`F`. -/
noncomputable def sectionsIsoExtZero :
    sheafSectionsOver (X := X) ⊤ ≅ extFunctorObj.{u} (constantSheafZ X) 0 :=
  NatIso.ofComponents (fun F => (constantSheafZExt₀Equiv X F).symm.toAddCommGrpIso)
    (fun {F G} f => by
    ext x
    change (constantSheafZExt₀Equiv X G).symm (f.hom.app (op ⊤) x) =
      ((constantSheafZExt₀Equiv X F).symm x).comp (Ext.mk₀ f) (add_zero 0)
    rw [AddEquiv.symm_apply_eq, constantSheafZExt₀Equiv_apply, constantSheafZ_addEquiv₀_comp_mk₀]
    change _ = f.hom.app (op ⊤)
      (constantSheafZExt₀Equiv X F ((constantSheafZExt₀Equiv X F).symm x))
    exact congrArg _ ((constantSheafZExt₀Equiv X F).apply_symm_apply x).symm)

/-- **Sheaf cohomology as Ext from the constant sheaf.** For a topological space `X` and
`n : ℕ`, an isomorphism `H^n(X,F) ≅ Ext^n(ℤ_X,F)` natural in the abelian sheaf `F`, where
`H^n(X,-) = R^nΓ(X,-)` is Hartshorne's sheaf cohomology and `Ext^n(ℤ_X,F)` is the Ext group of
the abelian category of abelian sheaves on `X` (Mathlib's `Abelian.Ext`; the same groups as
`CategoryTheory.Sheaf.H F n`). It is the canonical identification in degree zero
(`Hartshorne.sheafCohomologyIsoExt_zero`) and commutes with the connecting homomorphisms
(`Hartshorne.sheafCohomologyIsoExt_δ`). -/
noncomputable def sheafCohomologyIsoExt (n : ℕ) :
    sheafCohomology X n ≅ extFunctorObj.{u} (constantSheafZ X) n :=
  compIso (sheafCohomologyEffaceable X) (extEffaceable X)
    (sheafCohomologyZeroIso X ≪≫ sectionsIsoExtZero X) n

/-- In degree zero, `H^0(X,F) ≅ Ext^0(ℤ_X,F) = Hom(ℤ_X,F)` followed by evaluation at the global
section `1` of `ℤ_X` is the identification `H^0(X,F) ≅ Γ(X,F)`. -/
theorem sheafCohomologyIsoExt_zero (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : (sheafCohomology X 0).obj F) :
    (Ext.addEquiv₀ ((sheafCohomologyIsoExt X 0).hom.app F x)).hom.app (op ⊤)
        (constantSheafZOne X) =
      (sheafCohomologyZeroIso X).hom.app F x :=
  (constantSheafZExt₀Equiv X F).apply_symm_apply ((sheafCohomologyZeroIso X).hom.app F x)

/-- The isomorphisms `H^n(X,-) ≅ Ext^n(ℤ_X,-)` carry the connecting homomorphism
`H^n(X,F'') ⟶ H^{n+1}(X,F')` of a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` to the Yoneda
product `Ext^n(ℤ_X,F'') ⟶ Ext^{n+1}(ℤ_X,F')` with its class in `Ext^1(F'',F')`. -/
theorem sheafCohomologyIsoExt_δ {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ) :
    rightDerivedδ (sheafSectionsOver (X := X) ⊤) hS n ≫
        (sheafCohomologyIsoExt X (n + 1)).hom.app S.X₁ =
      (sheafCohomologyIsoExt X n).hom.app S.X₃ ≫
        AddCommGrpCat.ofHom (hS.extClass.{u}.postcomp (constantSheafZ X) rfl) :=
  δ_compIso_hom (sheafCohomologyEffaceable X) (extEffaceable X) _ hS n

end Sheaf

end Hartshorne
