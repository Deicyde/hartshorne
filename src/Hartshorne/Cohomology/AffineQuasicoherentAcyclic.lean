/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.TildeInjectiveFlasque
import Hartshorne.Cohomology.SheafCohomologyFlasque
import Hartshorne.Cohomology.ModuleCohomologyComparison
import Hartshorne.Scheme.AffineTildeLocalization
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Quasi-coherent sheaves on a Noetherian affine scheme are acyclic

Hartshorne, *Algebraic Geometry*, III, Theorem 3.5 (p. 215).

Let `X = Spec A` with `A` Noetherian and let `F` be a quasi-coherent `𝒪_X`-module. Then
`H^i(X, F) = 0` for every `i > 0`, where the cohomology of `F` is that of its underlying abelian
sheaf (`Hartshorne.sheafCohomology_isZero_of_isQuasicoherent_spec`).

The same vanishing holds on every affine scheme `X` that is (locally) Noetherian
(`Hartshorne.sheafCohomology_isZero_of_isQuasicoherent_of_isAffine`): transport along the
isomorphism `X ≅ Spec Γ(X, 𝒪_X)`, using that sheaf cohomology is invariant under homeomorphisms
(`Hartshorne.sheafCohomologyPushforwardIsoOfIso`).

## Proof

Since `F` is quasi-coherent, `F ≅ M~` with `M = Γ(X, F)`. We show `H^{n+1}(X, M~) = 0` for every
`A`-module `M`, by induction on `n`. Embed `M` into an injective `A`-module `I`. Tilde is exact, and
so is passing to the underlying abelian sheaf, so `0 ⟶ M~ ⟶ I~ ⟶ (I/M)~ ⟶ 0` is a short exact
sequence of abelian sheaves. The sheaf `I~` is flasque (Proposition III.3.4), hence acyclic.
In degree one, `Γ(X, I~) ⟶ Γ(X, (I/M)~)` is the surjection `I ⟶ I/M`, so the connecting map
`Γ(X, (I/M)~) ⟶ H^1(X, M~)` vanishes and `H^1(X, M~) = 0`. In higher degrees,
`H^{n+1}(X, (I/M)~) ⟶ H^{n+2}(X, M~) ⟶ H^{n+2}(X, I~) = 0` is exact and the first group vanishes
by induction.
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace Hartshorne

namespace AffineAcyclic

variable {A : CommRingCat.{u}}

-- The global section functor `Γ(X, -)` on abelian sheaves over `Spec A`.
set_option hygiene false in
local notation "Γ₀" => sheafSectionsOver (X := (Spec (.of A)).toTopCat) ⊤

/-- The short exact sequence `0 ⟶ M ⟶ I ⟶ I/M ⟶ 0` with `I` the chosen injective hull. -/
noncomputable abbrev injectiveSC (M : ModuleCat.{u} A) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)

theorem injectiveSC_shortExact (M : ModuleCat.{u} A) : (injectiveSC M).ShortExact :=
  ShortComplex.ShortExact.mk' ((injectiveSC M).exact_of_g_is_cokernel (cokernelIsCokernel _))
    inferInstance inferInstance

/-- The short exact sequence `0 ⟶ M~ ⟶ I~ ⟶ (I/M)~ ⟶ 0` of `𝒪_{Spec A}`-modules. -/
noncomputable abbrev tildeSCMod (M : ModuleCat.{u} A) :
    ShortComplex (SheafOfModules.{u} (Spec (.of A)).ringCatSheaf) :=
  ((injectiveSC M).map (tilde.functor A) : ShortComplex (Spec (.of A)).Modules)

theorem tildeSCMod_shortExact (M : ModuleCat.{u} A) : (tildeSCMod M).ShortExact :=
  (affineTilde_exact A).2.1 _ (injectiveSC_shortExact M)

/-- The underlying short exact sequence of abelian sheaves `0 ⟶ M~ ⟶ I~ ⟶ (I/M)~ ⟶ 0`. -/
noncomputable abbrev tildeSC (M : ModuleCat.{u} A) :=
  (tildeSCMod M).map (ModuleCohomology.toTopSheaf (Spec (.of A)).ringCatSheaf)

theorem tildeSC_shortExact (M : ModuleCat.{u} A) : (tildeSC M).ShortExact :=
  (tildeSCMod_shortExact M).map_of_exact _

/-- `Γ(X, I~) ⟶ Γ(X, (I/M)~)` is surjective. -/
theorem epi_globalSections_tildeSC_g (M : ModuleCat.{u} A) : Epi ((Γ₀).map (tildeSC M).g) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro t
  set N := cokernel (Injective.ι M)
  set I := Injective.under M
  obtain ⟨n, rfl⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen N ⊤)).2 t
  obtain ⟨m, rfl⟩ := (ModuleCat.epi_iff_surjective (cokernel.π (Injective.ι M))).1 inferInstance n
  refine ⟨tilde.toOpen I ⊤ m, ?_⟩
  exact ConcreteCategory.congr_hom (tilde.toOpen_map_app (cokernel.π (Injective.ι M)) ⊤) m

variable [IsNoetherianRing A]

theorem isFlasque_tildeSC_X₂ (M : ModuleCat.{u} A) : (tildeSC M).X₂.IsFlasque := by
  have : Injective (ModuleCat.of A (injectiveSC M).X₂) :=
    inferInstanceAs (Injective (Injective.under M))
  have : Module.Injective A (injectiveSC M).X₂ :=
    Module.injective_module_of_injective_object _ _
  exact tilde_isFlasque (injectiveSC M).X₂

/-- `H^{n+1}(Spec A, M~) = 0` for every `A`-module `M`. -/
theorem isZero_tilde (n : ℕ) : ∀ M : ModuleCat.{u} A,
    IsZero ((sheafCohomology (Spec (.of A)).toTopCat (n + 1)).obj
      ((ModuleCohomology.toTopSheaf (Spec (.of A)).ringCatSheaf).obj (tilde M))) := by
  induction n with
  | zero =>
    intro M
    have hS := tildeSC_shortExact M
    have := isFlasque_tildeSC_X₂ M
    have hI : IsZero ((sheafCohomology (Spec (.of A)).toTopCat (0 + 1)).obj (tildeSC M).X₂) :=
      sheafCohomology_isZero_of_isFlasque _ 0
    have hepi0 : Epi (((Γ₀).rightDerived 0).map (tildeSC M).g) := by
      have hepi := epi_globalSections_tildeSC_g M
      have hnat := ((Γ₀).rightDerivedZeroIsoSelf).hom.naturality (tildeSC M).g
      have e : ((Γ₀).rightDerived 0).map (tildeSC M).g =
          ((Γ₀).rightDerivedZeroIsoSelf).hom.app (tildeSC M).X₂ ≫ (Γ₀).map (tildeSC M).g ≫
            ((Γ₀).rightDerivedZeroIsoSelf).inv.app (tildeSC M).X₃ := by
        rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      rw [e]
      infer_instance
    have hδ : rightDerivedδ Γ₀ hS 0 = 0 :=
      (cancel_epi (((Γ₀).rightDerived 0).map (tildeSC M).g)).1
        (by rw [comp_zero]; exact RightDerivedLES.Horseshoe.map_g_comp_δ Γ₀ hS _ _ 0)
    have hδepi : Epi (rightDerivedδ Γ₀ hS 0) :=
      (rightDerived_exact₁ Γ₀ hS 0).epi_f (hI.eq_of_tgt _ _)
    rw [hδ] at hδepi
    exact IsZero.of_epi_zero (((Γ₀).rightDerived 0).obj (tildeSC M).X₃)
      (((Γ₀).rightDerived (0 + 1)).obj (tildeSC M).X₁)
  | succ n ih =>
    intro M
    have hS := tildeSC_shortExact M
    have := isFlasque_tildeSC_X₂ M
    have hI : IsZero ((sheafCohomology (Spec (.of A)).toTopCat (n + 1 + 1)).obj (tildeSC M).X₂) :=
      sheafCohomology_isZero_of_isFlasque _ (n + 1)
    have hN : IsZero ((sheafCohomology (Spec (.of A)).toTopCat (n + 1)).obj (tildeSC M).X₃) :=
      ih (cokernel (Injective.ι M))
    exact (rightDerived_exact₁ Γ₀ hS (n + 1)).isZero_of_both_zeros (hN.eq_of_src _ _)
      (hI.eq_of_tgt _ _)

end AffineAcyclic

open AffineAcyclic in
/-- **Hartshorne III, Theorem 3.5.** Let `X = Spec A` with `A` Noetherian and let `F` be a
quasi-coherent `𝒪_X`-module. Then `H^i(X, F) = 0` for every `i > 0`; here `H^i(X, F)` is the
sheaf cohomology of the underlying abelian sheaf of `F`. -/
theorem sheafCohomology_isZero_of_isQuasicoherent_spec {A : CommRingCat.{u}} [IsNoetherianRing A]
    (F : (Spec A).Modules) [F.IsQuasicoherent] (i : ℕ) (hi : 0 < i) :
    IsZero ((sheafCohomology (Spec A).toTopCat i).obj
      ((SheafOfModules.toSheaf (Spec A).ringCatSheaf).obj F)) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have : IsIso F.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ F).mp inferInstance
  let G : (Spec (.of A)).Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} (Spec (.of A)).toTopCat :=
    ModuleCohomology.toTopSheaf (Spec (.of A)).ringCatSheaf
  exact (isZero_tilde n _).of_iso
    ((sheafCohomology _ (n + 1)).mapIso (G.mapIso (asIso F.fromTildeΓ))).symm

section Transport

variable {C : Type*} [Category* C] [Abelian C] [HasInjectiveResolutions C]
  {C' : Type*} [Category* C'] [Abelian C'] [HasInjectiveResolutions C']
  {D : Type*} [Category* D] [Abelian D]

/-- Right derived functors are compatible with precomposition by an additive equivalence:
`Rⁿ Γ' (E A) ≅ Rⁿ (E ⋙ Γ') A`. The image under `E` of an injective resolution of `A` is an
injective resolution of `E A`. -/
noncomputable def rightDerivedObjIsoOfIsEquivalence (E : C ⥤ C') [E.IsEquivalence] [E.Additive]
    (Γ' : C' ⥤ D) [Γ'.Additive] (A : C) (n : ℕ) :
    (Γ'.rightDerived n).obj (E.obj A) ≅ ((E ⋙ Γ').rightDerived n).obj A := by
  let I := injectiveResolution A
  let J : InjectiveResolution (E.obj A) :=
    { cocomplex := (E.mapHomologicalComplex _).obj I.cocomplex
      injective := fun n => E.injective_obj (I.cocomplex.X n)
      ι := (HomologicalComplex.singleMapHomologicalComplex E (ComplexShape.up ℕ) 0).inv.app A ≫
        (E.mapHomologicalComplex _).map I.ι
      quasiIso := inferInstance }
  exact J.isoRightDerivedObj Γ' n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (Iso.refl _) ≪≫
    (I.isoRightDerivedObj (E ⋙ Γ') n).symm

end Transport

section TopTransport

variable {X Y : TopCat.{u}}

/-- A homeomorphism gives an equivalence of categories of abelian sheaves. -/
noncomputable def sheafEquivOfIso (H : X ≅ Y) :
    TopCat.Sheaf AddCommGrpCat.{u} X ≌ TopCat.Sheaf AddCommGrpCat.{u} Y :=
  CategoryTheory.Equivalence.mk (TopCat.Sheaf.pushforward _ H.hom)
    (TopCat.Sheaf.pushforward _ H.inv)
    (NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      ((TopCat.Presheaf.presheafEquivOfIso _ H).unitIso.app F.obj))
      (fun f ↦ Sheaf.hom_ext
        ((TopCat.Presheaf.presheafEquivOfIso _ H).unitIso.hom.naturality f.hom)))
    (NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      ((TopCat.Presheaf.presheafEquivOfIso _ H).counitIso.app F.obj))
      (fun f ↦ Sheaf.hom_ext
        ((TopCat.Presheaf.presheafEquivOfIso _ H).counitIso.hom.naturality f.hom)))

/-- Sheaf cohomology is invariant under homeomorphisms: `H^n(Y, H_* F) ≅ H^n(X, F)`. -/
noncomputable def sheafCohomologyPushforwardIsoOfIso (H : X ≅ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (sheafCohomology Y n).obj ((TopCat.Sheaf.pushforward _ H.hom).obj F) ≅
      (sheafCohomology X n).obj F :=
  haveI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} H.hom).IsEquivalence :=
    (sheafEquivOfIso H).isEquivalence_functor
  haveI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} H.hom).Additive :=
    Functor.additive_of_preserves_binary_products _
  rightDerivedObjIsoOfIsEquivalence (TopCat.Sheaf.pushforward _ H.hom)
    (sheafSectionsOver (X := Y) ⊤) F n

end TopTransport

/-- Pushforward along an isomorphism of schemes preserves quasi-coherence. -/
private lemma isQuasicoherent_pushforward_of_isIso' {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    (G : X.Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e).obj G).IsQuasicoherent := by
  let u := (Scheme.Modules.restrictAdjunction e).unit.app (G.restrict (inv e))
  have hu : IsIso u := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro T
    simp only [u, Scheme.Modules.restrictAdjunction_unit_app_app]
    have key : ∀ (M : Y.Modules) {U V : Y.Opens} (h : U ≤ V) (_ : V ≤ U),
        IsIso (M.presheaf.map (homOfLE h).op) := fun M U V h h' ↦ by
      have : IsIso (homOfLE h) := ⟨⟨homOfLE h', Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
      infer_instance
    refine key _ _ ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso]
    simp
  let e₂ : (G.restrict (inv e)).restrict e ≅ G :=
    ((Scheme.Modules.restrictFunctorComp e (inv e)).app G).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (IsIso.hom_inv_id e)).app G ≪≫
        Scheme.Modules.restrictFunctorId.app G
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ u hu ≪≫ (Scheme.Modules.pushforward e).mapIso e₂)
    (inferInstanceAs ((G.restrict (inv e)).IsQuasicoherent))

/-- **Hartshorne III, Theorem 3.5, for an affine scheme.** Let `X` be an affine scheme which is
(locally) Noetherian, so that `X ≅ Spec A` with `A = Γ(X, 𝒪_X)` Noetherian, and let `F` be a
quasi-coherent `𝒪_X`-module. Then `H^i(X, F) = 0` for every `i > 0`; here `H^i(X, F)` is the
sheaf cohomology of the underlying abelian sheaf of `F`. -/
theorem sheafCohomology_isZero_of_isQuasicoherent_of_isAffine {X : Scheme.{u}} [IsAffine X]
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) (hi : 0 < i) :
    IsZero ((sheafCohomology X.toTopCat i).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)) := by
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have := isQuasicoherent_pushforward_of_isIso' X.isoSpec.hom F
  exact (sheafCohomology_isZero_of_isQuasicoherent_spec
    ((Scheme.Modules.pushforward X.isoSpec.hom).obj F) i hi).of_iso
      (sheafCohomologyPushforwardIsoOfIso (Scheme.forgetToTop.mapIso X.isoSpec) _ i).symm

end Hartshorne
