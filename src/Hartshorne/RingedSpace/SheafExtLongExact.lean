/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.RightDerivedLongExactSequence
import Hartshorne.RingedSpace.SheafExt

/-!
# The covariant long exact sequence of sheaf `ℰxt`

Hartshorne, *Algebraic Geometry*, III.6 (p. 233).

Let `(X, 𝒪_X)` be a ringed space and `F` an `𝒪_X`-module. Since `ℰxtⁿ(F, -)` is the `n`-th right
derived functor of the left exact functor `ℋom(F, -)`, a short exact sequence
`0 ⟶ G' ⟶ G ⟶ G'' ⟶ 0` of `𝒪_X`-modules gives a long exact sequence

`0 ⟶ ℋom(F, G') ⟶ ℋom(F, G) ⟶ ℋom(F, G'') ⟶ ℰxt¹(F, G') ⟶ ℰxt¹(F, G) ⟶ ℰxt¹(F, G'') ⟶ ⋯`
`⋯ ⟶ ℰxtⁿ(F, G') ⟶ ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F, G'') ⟶ ℰxtⁿ⁺¹(F, G') ⟶ ⋯`.

The connecting morphisms `ℰxtⁿ(F, G'') ⟶ ℰxtⁿ⁺¹(F, G')` (`Hartshorne.Ringed.sheafExtδ`) are those of
the long exact sequence of right derived functors (`Hartshorne.rightDerivedδ`). In degree zero the
sequence starts with the sheaf Hom terms themselves: the first connecting morphism
`ℋom(F, G'') ⟶ ℰxt¹(F, G')` (`Hartshorne.Ringed.sheafHomδ`) is the canonical map
`ℋom(F, G'') ⟶ ℰxt⁰(F, G'')`, an isomorphism because `ℋom(F, -)` is left exact, followed by the
connecting morphism `ℰxt⁰(F, G'') ⟶ ℰxt¹(F, G')`.

Exactness at every spot is `Hartshorne.Ringed.sheafHom_mono_map_f`,
`Hartshorne.Ringed.sheafHom_exact₂`, `Hartshorne.Ringed.sheafHom_exact₃`,
`Hartshorne.Ringed.sheafHom_exact₁`, `Hartshorne.Ringed.sheafExt_exact₂`,
`Hartshorne.Ringed.sheafExt_exact₃` and `Hartshorne.Ringed.sheafExt_exact₁`; the connecting
morphisms are natural in morphisms of short exact sequences
(`Hartshorne.Ringed.sheafHomδ_naturality`, `Hartshorne.Ringed.sheafExtδ_naturality`).

## Implementation note

The statements for module sheaves are instances of statements about an arbitrary additive functor
`G` on an abelian category, a family of functors `E n` equal to its right derived functors and a
family `d` of morphisms equal to its connecting morphisms transported along these equalities by
`eqToHom` (namespace `Hartshorne.Ringed.SheafExtLongExact`). Each specialized statement is then
syntactically an instance of a general one. Checking a specialization against differently
elaborated instance arguments (the additivity of `ℋom(F, -)` for the preadditive structure the
category carries directly rather than the one underlying its abelian structure, or instance
proofs abstracted into auxiliary lemmas) makes the kernel unfold the large abelian structure of
module sheaves, which takes minutes per declaration; the two instances are therefore restated
once, as local instances.
-/

universe u v' u'

open CategoryTheory Limits

namespace Hartshorne

namespace Ringed

namespace SheafExtLongExact

variable {C : Type u'} [Category.{v'} C] [Abelian C] [HasInjectiveResolutions C]
  (G : C ⥤ C) [G.Additive] (E : ℕ → C ⥤ C) (hE : ∀ n, G.rightDerived n = E n)

/-- The connecting morphism `RⁿG(A'') ⟶ Rⁿ⁺¹G(A')`, transported to functors `E n` equal to the
right derived functors of `G`. -/
noncomputable def δ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (E n).obj S.X₃ ⟶ (E (n + 1)).obj S.X₁ :=
  eqToHom (Functor.congr_obj (hE n).symm S.X₃) ≫ rightDerivedδ G hS n ≫
    eqToHom (Functor.congr_obj (hE (n + 1)) S.X₁)

/-- The canonical map `G ⟶ R⁰G`, transported to a functor `E 0` equal to `R⁰G`. -/
noncomputable def η : G ⟶ E 0 :=
  G.toRightDerivedZero ≫ eqToHom (hE 0)

lemma η_app_comp_map {X Y : C} (f : X ⟶ Y) :
    (η G E hE).app X ≫ (E 0).map f = G.map f ≫ (η G E hE).app Y :=
  ((η G E hE).naturality f).symm

lemma δ_self {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    δ G G.rightDerived (fun _ ↦ rfl) hS n = rightDerivedδ G hS n := by
  simp [δ]

lemma η_self : η G G.rightDerived (fun _ ↦ rfl) = G.toRightDerivedZero := by
  simp [η]

include hE

lemma map_f_comp_map_g {S : ShortComplex C} (n : ℕ) : (E n).map S.f ≫ (E n).map S.g = 0 := by
  obtain rfl : G.rightDerived = E := funext hE
  rw [← Functor.map_comp, S.zero, Functor.map_zero]

lemma map_g_comp_δ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (E n).map S.g ≫ δ G E hE hS n = 0 := by
  obtain rfl : G.rightDerived = E := funext hE
  rw [δ_self]
  exact RightDerivedLES.Horseshoe.map_g_comp_δ G hS _ _ n

lemma δ_comp_map_f {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    δ G E hE hS n ≫ (E (n + 1)).map S.f = 0 := by
  obtain rfl : G.rightDerived = E := funext hE
  rw [δ_self]
  exact RightDerivedLES.Horseshoe.δ_comp_map_f G hS _ _ n

lemma exact₂ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (w : (E n).map S.f ≫ (E n).map S.g = 0) :
    (ShortComplex.mk ((E n).map S.f) ((E n).map S.g) w).Exact := by
  obtain rfl : G.rightDerived = E := funext hE
  exact rightDerived_exact₂ G hS n

lemma exact₃ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (w : (E n).map S.g ≫ δ G E hE hS n = 0) :
    (ShortComplex.mk ((E n).map S.g) (δ G E hE hS n) w).Exact := by
  obtain rfl : G.rightDerived = E := funext hE
  revert w
  rw [δ_self]
  intro w
  exact rightDerived_exact₃ G hS n

lemma exact₁ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (w : δ G E hE hS n ≫ (E (n + 1)).map S.f = 0) :
    (ShortComplex.mk (δ G E hE hS n) ((E (n + 1)).map S.f) w).Exact := by
  obtain rfl : G.rightDerived = E := funext hE
  revert w
  rw [δ_self]
  intro w
  exact rightDerived_exact₁ G hS n

lemma δ_naturality {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (n : ℕ) :
    δ G E hE hS₁ n ≫ (E (n + 1)).map φ.τ₁ = (E n).map φ.τ₃ ≫ δ G E hE hS₂ n := by
  obtain rfl : G.rightDerived = E := funext hE
  rw [δ_self, δ_self]
  exact rightDerivedδ_naturality G φ hS₁ hS₂ n

lemma map_g_comp_η_app_comp_δ {S : ShortComplex C} (hS : S.ShortExact) :
    G.map S.g ≫ (η G E hE).app S.X₃ ≫ δ G E hE hS 0 = 0 := by
  rw [← Category.assoc, ← η_app_comp_map, Category.assoc, map_g_comp_δ G E hE hS 0, comp_zero]

lemma η_app_comp_δ_comp_map_f {S : ShortComplex C} (hS : S.ShortExact) :
    ((η G E hE).app S.X₃ ≫ δ G E hE hS 0) ≫ (E 1).map S.f = 0 := by
  rw [Category.assoc, δ_comp_map_f G E hE hS 0, comp_zero]

lemma η_app_comp_δ_naturality {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) :
    ((η G E hE).app S₁.X₃ ≫ δ G E hE hS₁ 0) ≫ (E 1).map φ.τ₁ =
      G.map φ.τ₃ ≫ (η G E hE).app S₂.X₃ ≫ δ G E hE hS₂ 0 := by
  rw [Category.assoc, δ_naturality G E hE φ hS₁ hS₂ 0, ← Category.assoc, ← Category.assoc,
    η_app_comp_map]

variable [PreservesFiniteLimits G]

omit hE in
lemma mono_map_f {S : ShortComplex C} (hS : S.ShortExact) : Mono (G.map S.f) := by
  have := rightDerived_mono_map_f G hS
  have : Mono (G.map S.f ≫ G.toRightDerivedZero.app S.X₂) := by
    rw [G.toRightDerivedZero.naturality]; infer_instance
  exact mono_of_mono _ (G.toRightDerivedZero.app S.X₂)

omit hE in
lemma hom_exact₂ {S : ShortComplex C} (hS : S.ShortExact) (w : G.map S.f ≫ G.map S.g = 0) :
    (ShortComplex.mk (G.map S.f) (G.map S.g) w).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 (rightDerived_exact₂ G hS 0)
  exact ShortComplex.isoMk (asIso (G.toRightDerivedZero.app S.X₁))
    (asIso (G.toRightDerivedZero.app S.X₂)) (asIso (G.toRightDerivedZero.app S.X₃))
    (G.toRightDerivedZero.naturality S.f).symm (G.toRightDerivedZero.naturality S.g).symm

lemma hom_exact₃ {S : ShortComplex C} (hS : S.ShortExact)
    (w : G.map S.g ≫ (η G E hE).app S.X₃ ≫ δ G E hE hS 0 = 0) :
    (ShortComplex.mk (G.map S.g) ((η G E hE).app S.X₃ ≫ δ G E hE hS 0) w).Exact := by
  obtain rfl : G.rightDerived = E := funext hE
  revert w
  rw [δ_self, η_self]
  intro w
  refine (ShortComplex.exact_iff_of_iso ?_).2 (rightDerived_exact₃ G hS 0)
  exact ShortComplex.isoMk (asIso (G.toRightDerivedZero.app S.X₂))
    (asIso (G.toRightDerivedZero.app S.X₃)) (Iso.refl _)
    (G.toRightDerivedZero.naturality S.g).symm (by simp)

lemma hom_exact₁ {S : ShortComplex C} (hS : S.ShortExact)
    (w : ((η G E hE).app S.X₃ ≫ δ G E hE hS 0) ≫ (E 1).map S.f = 0) :
    (ShortComplex.mk ((η G E hE).app S.X₃ ≫ δ G E hE hS 0) ((E 1).map S.f) w).Exact := by
  obtain rfl : G.rightDerived = E := funext hE
  revert w
  rw [δ_self, η_self]
  intro w
  refine (ShortComplex.exact_iff_of_iso ?_).2 (rightDerived_exact₁ G hS 0)
  exact ShortComplex.isoMk (asIso (G.toRightDerivedZero.app S.X₃)) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp)

end SheafExtLongExact

namespace SheafExtLongExact

/-! The same statements for a family of morphisms `d` equal to the transported connecting
morphisms, so that they apply verbatim to named connecting morphisms. -/

variable {C : Type u'} [Category.{v'} C] [Abelian C] [HasInjectiveResolutions C]
  (G : C ⥤ C) [G.Additive] (E : ℕ → C ⥤ C) (hE : ∀ n, G.rightDerived n = E n)
  (d : ∀ {S : ShortComplex C} (_ : S.ShortExact) (n : ℕ), (E n).obj S.X₃ ⟶ (E (n + 1)).obj S.X₁)
  (hd : ∀ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ), d hS n = δ G E hE hS n)

include hd

lemma map_g_comp_d {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (E n).map S.g ≫ d hS n = 0 := by
  rw [hd]; exact map_g_comp_δ G E hE hS n

lemma d_comp_map_f {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    d hS n ≫ (E (n + 1)).map S.f = 0 := by
  rw [hd]; exact δ_comp_map_f G E hE hS n

lemma exact₃_d {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (w : (E n).map S.g ≫ d hS n = 0) : (ShortComplex.mk ((E n).map S.g) (d hS n) w).Exact := by
  revert w; rw [hd]; intro w; exact exact₃ G E hE hS n w

lemma exact₁_d {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (w : d hS n ≫ (E (n + 1)).map S.f = 0) :
    (ShortComplex.mk (d hS n) ((E (n + 1)).map S.f) w).Exact := by
  revert w; rw [hd]; intro w; exact exact₁ G E hE hS n w

lemma d_naturality {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (n : ℕ) :
    d hS₁ n ≫ (E (n + 1)).map φ.τ₁ = (E n).map φ.τ₃ ≫ d hS₂ n := by
  rw [hd, hd]; exact δ_naturality G E hE φ hS₁ hS₂ n

omit hd in
/-- The connecting morphism `G(A'') ⟶ R¹G(A')`: the canonical map `G ⟶ R⁰G` followed by the
connecting morphism in degree zero, for a family `d` of connecting morphisms. -/
noncomputable def homδ {S : ShortComplex C} (hS : S.ShortExact) : G.obj S.X₃ ⟶ (E 1).obj S.X₁ :=
  (η G E hE).app S.X₃ ≫ d hS 0

lemma map_g_comp_homδ {S : ShortComplex C} (hS : S.ShortExact) :
    G.map S.g ≫ homδ G E hE d hS = 0 := by
  rw [homδ, hd]; exact map_g_comp_η_app_comp_δ G E hE hS

lemma homδ_comp_map_f {S : ShortComplex C} (hS : S.ShortExact) :
    homδ G E hE d hS ≫ (E 1).map S.f = 0 := by
  rw [homδ, hd]; exact η_app_comp_δ_comp_map_f G E hE hS

lemma homδ_naturality {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) :
    homδ G E hE d hS₁ ≫ (E 1).map φ.τ₁ = G.map φ.τ₃ ≫ homδ G E hE d hS₂ := by
  rw [homδ, homδ, hd, hd]; exact η_app_comp_δ_naturality G E hE φ hS₁ hS₂

variable [PreservesFiniteLimits G]

lemma hom_exact₃_d {S : ShortComplex C} (hS : S.ShortExact)
    (w : G.map S.g ≫ homδ G E hE d hS = 0) :
    (ShortComplex.mk (G.map S.g) (homδ G E hE d hS) w).Exact := by
  revert w; rw [homδ, hd]; intro w; exact hom_exact₃ G E hE hS w

lemma hom_exact₁_d {S : ShortComplex C} (hS : S.ShortExact)
    (w : homδ G E hE d hS ≫ (E 1).map S.f = 0) :
    (ShortComplex.mk (homδ G E hE d hS) ((E 1).map S.f) w).Exact := by
  revert w; rw [homδ, hd]; intro w; exact hom_exact₁ G E hE hS w

end SheafExtLongExact

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

attribute [local instance 2000] Abelian.toPreadditive

/-- The additivity of `ℋom(F, -)`, stated for the preadditive structure underlying the abelian
structure of the category of module sheaves. -/
private theorem moduleSheafHomFunctor_additive' (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    @Functor.Additive _ _ _ _ (@Abelian.toPreadditive _ _ sheafOfModules_abelian)
      (@Abelian.toPreadditive _ _ sheafOfModules_abelian) (moduleSheafHomFunctor F) :=
  moduleSheafHomFunctor_additive F

attribute [local instance 3000] moduleSheafHomFunctor_additive'

/-- Injective resolutions of module sheaves, as a single constant: otherwise each definition
below would abstract the instance term into its own auxiliary proof, and the kernel would have
to compare these proofs' types. -/
private theorem sheafOfModules_hasInjectiveResolutions :
    HasInjectiveResolutions (SheafOfModules.{u} (ringCatSheafOf R)) :=
  inferInstance

attribute [local instance 3000] sheafOfModules_hasInjectiveResolutions

private theorem rightDerived_eq_sheafExt (F : SheafOfModules.{u} (ringCatSheafOf R)) (n : ℕ) :
    (moduleSheafHomFunctor F).rightDerived n = sheafExt F n :=
  rfl

variable (F : SheafOfModules.{u} (ringCatSheafOf R))
  {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))} (hS : S.ShortExact)

/-- The connecting morphism `ℰxtⁿ(F, G'') ⟶ ℰxtⁿ⁺¹(F, G')` attached to a short exact sequence
`0 ⟶ G' ⟶ G ⟶ G'' ⟶ 0` of `𝒪_X`-modules (Hartshorne III.6, p. 233): the connecting morphism
`Hartshorne.rightDerivedδ` of the long exact sequence of the right derived functors of
`ℋom(F, -)`, which are the functors `ℰxtⁿ(F, -)` by definition. -/
noncomputable def sheafExtδ (n : ℕ) : (sheafExt F n).obj S.X₃ ⟶ (sheafExt F (n + 1)).obj S.X₁ :=
  SheafExtLongExact.δ (moduleSheafHomFunctor F) (sheafExt F) (rightDerived_eq_sheafExt F) hS n

/-- The first connecting morphism `ℋom(F, G'') ⟶ ℰxt¹(F, G')` of the covariant long exact sequence
attached to a short exact sequence `0 ⟶ G' ⟶ G ⟶ G'' ⟶ 0`: the canonical map
`ℋom(F, G'') ⟶ ℰxt⁰(F, G'')` (Mathlib's `Functor.toRightDerivedZero`) followed by the connecting
morphism `ℰxt⁰(F, G'') ⟶ ℰxt¹(F, G')`. -/
noncomputable def sheafHomδ : (moduleSheafHomFunctor F).obj S.X₃ ⟶ (sheafExt F 1).obj S.X₁ :=
  SheafExtLongExact.homδ (moduleSheafHomFunctor F) (sheafExt F) (rightDerived_eq_sheafExt F)
    (sheafExtδ F) hS

/-- The composite `ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F, G'') ⟶ ℰxtⁿ⁺¹(F, G')` vanishes. -/
@[reassoc]
lemma map_g_comp_sheafExtδ (n : ℕ) : (sheafExt F n).map S.g ≫ sheafExtδ F hS n = 0 :=
  SheafExtLongExact.map_g_comp_d (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) hS n

/-- The composite `ℰxtⁿ(F, G'') ⟶ ℰxtⁿ⁺¹(F, G') ⟶ ℰxtⁿ⁺¹(F, G)` vanishes. -/
@[reassoc]
lemma sheafExtδ_comp_map_f (n : ℕ) :
    sheafExtδ F hS n ≫ (sheafExt F (n + 1)).map S.f = 0 :=
  SheafExtLongExact.d_comp_map_f (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) hS n

include hS in
/-- **The covariant sequence starts with `0`** (Hartshorne III.6, p. 233): for a short exact
sequence `0 ⟶ G' ⟶ G ⟶ G'' ⟶ 0`, the map `ℋom(F, G') ⟶ ℋom(F, G)` is a monomorphism. -/
theorem sheafHom_mono_map_f : Mono ((moduleSheafHomFunctor F).map S.f) :=
  SheafExtLongExact.mono_map_f (moduleSheafHomFunctor F) hS

include hS in
/-- Exactness of `ℋom(F, G') ⟶ ℋom(F, G) ⟶ ℋom(F, G'')` (Hartshorne III.6, p. 233). -/
theorem sheafHom_exact₂ :
    (ShortComplex.mk ((moduleSheafHomFunctor F).map S.f) ((moduleSheafHomFunctor F).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact :=
  SheafExtLongExact.hom_exact₂ (moduleSheafHomFunctor F) hS _

/-- The composite `ℋom(F, G) ⟶ ℋom(F, G'') ⟶ ℰxt¹(F, G')` vanishes. -/
lemma map_g_comp_sheafHomδ : (moduleSheafHomFunctor F).map S.g ≫ sheafHomδ F hS = 0 :=
  SheafExtLongExact.map_g_comp_homδ (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) hS

/-- The composite `ℋom(F, G'') ⟶ ℰxt¹(F, G') ⟶ ℰxt¹(F, G)` vanishes. -/
lemma sheafHomδ_comp_map_f : sheafHomδ F hS ≫ (sheafExt F 1).map S.f = 0 :=
  SheafExtLongExact.homδ_comp_map_f (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) hS

/-- Exactness of `ℋom(F, G) ⟶ ℋom(F, G'') ⟶ ℰxt¹(F, G')` (Hartshorne III.6, p. 233). -/
theorem sheafHom_exact₃ :
    (ShortComplex.mk ((moduleSheafHomFunctor F).map S.g) (sheafHomδ F hS)
      (map_g_comp_sheafHomδ F hS)).Exact :=
  SheafExtLongExact.hom_exact₃_d (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) hS _

/-- Exactness of `ℋom(F, G'') ⟶ ℰxt¹(F, G') ⟶ ℰxt¹(F, G)` (Hartshorne III.6, p. 233). -/
theorem sheafHom_exact₁ :
    (ShortComplex.mk (sheafHomδ F hS) ((sheafExt F 1).map S.f)
      (sheafHomδ_comp_map_f F hS)).Exact :=
  SheafExtLongExact.hom_exact₁_d (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) hS _

include hS in
/-- Exactness of `ℰxtⁿ(F, G') ⟶ ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F, G'')` (Hartshorne III.6, p. 233). -/
theorem sheafExt_exact₂ (n : ℕ) :
    (ShortComplex.mk ((sheafExt F n).map S.f) ((sheafExt F n).map S.g)
      (SheafExtLongExact.map_f_comp_map_g (moduleSheafHomFunctor F) (sheafExt F)
        (rightDerived_eq_sheafExt F) n)).Exact :=
  SheafExtLongExact.exact₂ (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) hS n _

/-- Exactness of `ℰxtⁿ(F, G) ⟶ ℰxtⁿ(F, G'') ⟶ ℰxtⁿ⁺¹(F, G')` (Hartshorne III.6, p. 233). -/
theorem sheafExt_exact₃ (n : ℕ) :
    (ShortComplex.mk ((sheafExt F n).map S.g) (sheafExtδ F hS n)
      (map_g_comp_sheafExtδ F hS n)).Exact :=
  SheafExtLongExact.exact₃_d (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) hS n _

/-- Exactness of `ℰxtⁿ(F, G'') ⟶ ℰxtⁿ⁺¹(F, G') ⟶ ℰxtⁿ⁺¹(F, G)` (Hartshorne III.6, p. 233). -/
theorem sheafExt_exact₁ (n : ℕ) :
    (ShortComplex.mk (sheafExtδ F hS n) ((sheafExt F (n + 1)).map S.f)
      (sheafExtδ_comp_map_f F hS n)).Exact :=
  SheafExtLongExact.exact₁_d (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) hS n _

/-- **Naturality of the first connecting morphism** `ℋom(F, G'') ⟶ ℰxt¹(F, G')` in morphisms of
short exact sequences (Hartshorne III.6, p. 233). -/
theorem sheafHomδ_naturality {S₁ S₂ : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) :
    sheafHomδ F hS₁ ≫ (sheafExt F 1).map φ.τ₁ =
      (moduleSheafHomFunctor F).map φ.τ₃ ≫ sheafHomδ F hS₂ :=
  SheafExtLongExact.homδ_naturality (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) φ hS₁ hS₂

/-- **Naturality of the connecting morphisms** `ℰxtⁿ(F, G'') ⟶ ℰxtⁿ⁺¹(F, G')` in morphisms of
short exact sequences (Hartshorne III.6, p. 233). -/
theorem sheafExtδ_naturality {S₁ S₂ : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n : ℕ) :
    sheafExtδ F hS₁ n ≫ (sheafExt F (n + 1)).map φ.τ₁ =
      (sheafExt F n).map φ.τ₃ ≫ sheafExtδ F hS₂ n :=
  SheafExtLongExact.d_naturality (moduleSheafHomFunctor F) (sheafExt F)
    (rightDerived_eq_sheafExt F) (sheafExtδ F) (fun _ _ ↦ rfl) φ hS₁ hS₂ n

end Ringed

end Hartshorne
