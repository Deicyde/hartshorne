/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SheafSupport
import Hartshorne.Cohomology.AcyclicResolutionComparison
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Hartshorne.Cohomology.InjectiveAbelianSheafFlasque
import Hartshorne.Scheme.OpenExtensionByZeroAdjunction

/-!
# Cohomology with supports in a closed subset

Hartshorne, *Algebraic Geometry*, III, Exercise 2.3, p. 212.

For a closed subset `Y` of a topological space `X`, `Hartshorne.supportedSections Y hY` is the
functor `Γ_Y(X,-)` on abelian sheaves, the kernel of restriction `Γ(X,-) ⟶ Γ(X \ Y,-)`. Its
elements are exactly the global sections whose support lies in `Y`
(`Hartshorne.mem_range_supportedSections_iff`). It is left exact, and
`Hartshorne.cohomologyWithSupports Y hY n` is its `n`-th right derived functor `H^n_Y(X,-)`.
Flasque sheaves are `Γ_Y(X,-)`-acyclic
(`Hartshorne.isRightAcyclic_supportedSections_of_isFlasque`).

Sheaf cohomology `H^n(X,-)` is the right derived functor of global sections `Γ(X,-)`. For the
open complement `U = X \ Y`, the group `H^n(U,F|_U)` is the right derived functor of global
sections on `U` evaluated at the restriction `F|_U` (`Hartshorne.openRestrict`). The localization
sequence
`0 ⟶ H^0_Y(X,F) ⟶ H^0(X,F) ⟶ H^0(U,F|_U) ⟶ H^1_Y(X,F) ⟶ H^1(X,F) ⟶ ⋯`
is formed by the natural transformations `Hartshorne.cohomologyWithSupportsToCohomology`,
`Hartshorne.cohomologyRestriction` and `Hartshorne.localizationδ`, and it is exact
(`Hartshorne.cohomologyWithSupportsToCohomology_mono`, `Hartshorne.localization_exact₂`,
`Hartshorne.localization_exact₃`, `Hartshorne.localization_exact₁`).

For an injective resolution `I` of `F` the sheaves `I^k` are flasque, so
`0 ⟶ Γ_Y(X,I) ⟶ Γ(X,I) ⟶ Γ(U,I) ⟶ 0` is a short exact sequence of complexes, and the
localization sequence is its homology sequence. Restriction to `U` is exact and has a left adjoint,
extension by zero, which preserves monomorphisms; hence `I|_U` is an injective resolution of
`F|_U`, and `Γ(U,I) = Γ(U,I|_U)` computes `H^n(U,F|_U)`.
-/
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Hartshorne

open private openZeroFunctor from Hartshorne.Scheme.OpenExtensionByZeroAdjunction

section Acyclic

variable {C : Type*} [Category* C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- Dimension shifting: let `P` be a property of objects such that for every short exact
sequence `0 ⟶ A ⟶ I ⟶ G ⟶ 0` with `P A` and `I` injective, also `P G` holds and
`F(I) ⟶ F(G)` is an epimorphism. Then every object satisfying `P` is `F`-acyclic. -/
theorem isRightAcyclic_of_shortExact_injective (P : C → Prop)
    (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → Injective S.X₂ →
      P S.X₃ ∧ Epi (F.map S.g)) :
    ∀ A : C, P A → IsRightAcyclic F A := by
  have key : ∀ n : ℕ, ∀ A : C, P A → IsZero ((F.rightDerived (n + 1)).obj A) := by
    intro n
    induction n with
    | zero =>
      intro A hA
      let I := injectiveResolution A
      let S := ShortComplex.mk (RightDerivedLES.aug I) (cokernel.π (RightDerivedLES.aug I))
        (cokernel.condition _)
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel _))
          (inferInstanceAs (Mono (RightDerivedLES.aug I))) (inferInstanceAs (Epi (cokernel.π _)))
      obtain ⟨-, hepi⟩ := hP S hS hA (I.injective 0)
      have hepi0 : Epi ((F.rightDerived 0).map S.g) := by
        have := (F.rightDerivedZeroIsoSelf).hom.naturality S.g
        rw [← cancel_mono ((F.rightDerivedZeroIsoSelf).inv.app S.X₃)] at this
        have e : (F.rightDerived 0).map S.g = (F.rightDerivedZeroIsoSelf).hom.app S.X₂ ≫
            F.map S.g ≫ (F.rightDerivedZeroIsoSelf).inv.app S.X₃ := by
          simp
        rw [e]
        infer_instance
      have hI : IsZero ((F.rightDerived (0 + 1)).obj S.X₂) :=
        F.isZero_rightDerived_obj_injective_succ 0 S.X₂
      have hδ : rightDerivedδ F hS 0 = 0 :=
        (cancel_epi ((F.rightDerived 0).map S.g)).1
          (by rw [comp_zero]; exact RightDerivedLES.Horseshoe.map_g_comp_δ F hS _ _ 0)
      have hδepi : Epi (rightDerivedδ F hS 0) :=
        (rightDerived_exact₁ F hS 0).epi_f (hI.eq_of_tgt _ _)
      rw [hδ] at hδepi
      exact IsZero.of_epi_zero ((F.rightDerived 0).obj S.X₃) ((F.rightDerived (0 + 1)).obj S.X₁)
    | succ n ih =>
      intro A hA
      let I := injectiveResolution A
      let S := ShortComplex.mk (RightDerivedLES.aug I) (cokernel.π (RightDerivedLES.aug I))
        (cokernel.condition _)
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel _))
          (inferInstanceAs (Mono (RightDerivedLES.aug I))) (inferInstanceAs (Epi (cokernel.π _)))
      obtain ⟨hG, -⟩ := hP S hS hA (I.injective 0)
      have hI : IsZero ((F.rightDerived (n + 1 + 1)).obj S.X₂) :=
        F.isZero_rightDerived_obj_injective_succ (n + 1) S.X₂
      have hGz : IsZero ((F.rightDerived (n + 1)).obj S.X₃) := ih S.X₃ hG
      have hex := rightDerived_exact₁ F hS (n + 1)
      exact hex.isZero_of_both_zeros (hGz.eq_of_src _ _) (hI.eq_of_tgt _ _)
  exact fun A hA n => key n A hA

end Acyclic

section Supports

variable {X : TopCat.{u}}

/-- The open complement `X \ Y` of a closed subset `Y`. -/
def closedComplement (Y : Set X) (hY : IsClosed Y) : Opens X :=
  ⟨Yᶜ, hY.isOpen_compl⟩

/-- Sections over an open subset, as a functor on abelian sheaves. -/
noncomputable abbrev sheafSectionsOver (V : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ (evaluation _ _).obj (op V)

/-- Sections over an open subset preserve finite limits. -/
noncomputable instance sheafSectionsOver_preservesFiniteLimits (V : Opens X) :
    PreservesFiniteLimits (sheafSectionsOver V) := by
  have h₁ : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X) := inferInstance
  have h₂ : PreservesFiniteLimits ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)) :=
    inferInstance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂

/-- Restriction from global sections to sections over an open subset. -/
noncomputable def restrictGlobalSections (V : Opens X) :
    sheafSectionsOver (X := X) ⊤ ⟶ sheafSectionsOver V :=
  Functor.whiskerLeft _ ((evaluation _ _).map (homOfLE le_top).op)

/-- The restriction map at a sheaf is its restriction morphism. -/
@[simp]
lemma restrictGlobalSections_app (V : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (restrictGlobalSections V).app F = F.obj.map (homOfLE le_top).op :=
  rfl

/-- The functor `Γ_Y(X,-)` of global sections supported in the closed subset `Y`: the kernel of
restriction from `X` to `X \ Y`. -/
noncomputable def supportedSections (Y : Set X) (hY : IsClosed Y) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  kernel (restrictGlobalSections (closedComplement Y hY))

/-- `Γ_Y(X,-)` is left exact. -/
noncomputable instance supportedSections_preservesFiniteLimits (Y : Set X) (hY : IsClosed Y) :
    PreservesFiniteLimits (supportedSections Y hY) := by
  let P := parallelPair (restrictGlobalSections (closedComplement Y hY)) 0
  have : PreservesFiniteLimits P.flip := by
    apply preservesFiniteLimits_of_evaluation
    intro j
    have : PreservesFiniteLimits (P.obj j) := by
      cases j
      · exact (inferInstance : PreservesFiniteLimits (sheafSectionsOver (X := X) ⊤))
      · exact (inferInstance : PreservesFiniteLimits (sheafSectionsOver (closedComplement Y hY)))
    exact preservesFiniteLimits_of_natIso (flipCompEvaluation P j).symm
  exact preservesFiniteLimits_of_natIso (limitIsoFlipCompLim P).symm

/-- `Γ_Y(X,-)` is additive. -/
noncomputable instance supportedSections_additive (Y : Set X) (hY : IsClosed Y) :
    (supportedSections Y hY).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Cohomology with supports `H^n_Y(X,-)`: the right derived functors of `Γ_Y(X,-)`. -/
noncomputable def cohomologyWithSupports (Y : Set X) (hY : IsClosed Y) (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  (supportedSections Y hY).rightDerived n

/-- In degree zero, `H^0_Y(X,-) ≅ Γ_Y(X,-)`. -/
noncomputable def cohomologyWithSupportsZeroIso (Y : Set X) (hY : IsClosed Y) :
    cohomologyWithSupports Y hY 0 ≅ supportedSections Y hY :=
  Functor.rightDerivedZeroIsoSelf _

/-- The short complex `0 ⟶ Γ_Y(X,F) ⟶ Γ(X,F) ⟶ Γ(X \ Y,F)`. -/
@[simps!]
noncomputable abbrev supportedSectionsSC (Y : Set X) (hY : IsClosed Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk ((kernel.ι (restrictGlobalSections (closedComplement Y hY))).app F)
    ((restrictGlobalSections (closedComplement Y hY)).app F)
    (by rw [← NatTrans.comp_app, kernel.condition, NatTrans.app_zero])

/-- `Γ_Y(X,F)` is the kernel of `Γ(X,F) ⟶ Γ(X \ Y,F)`. -/
lemma supportedSectionsSC_exact (Y : Set X) (hY : IsClosed Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) : (supportedSectionsSC Y hY F).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι _ (kernel.condition (restrictGlobalSections (closedComplement Y hY))))
    ((evaluation _ _).obj F)).1
    (isLimitOfPreserves ((evaluation _ _).obj F) (kernelIsKernel _))

/-- `Γ_Y(X,F) ⟶ Γ(X,F)` is injective. -/
instance supportedSectionsSC_mono_f (Y : Set X) (hY : IsClosed Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Mono (supportedSectionsSC Y hY F).f := by
  dsimp [supportedSectionsSC]
  infer_instance

/-- For a flasque sheaf `F`, the sequence `0 ⟶ Γ_Y(X,F) ⟶ Γ(X,F) ⟶ Γ(X \ Y,F) ⟶ 0` is
exact. -/
theorem supportedSectionsSC_shortExact_of_isFlasque (Y : Set X) (hY : IsClosed Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    (supportedSectionsSC Y hY F).ShortExact where
  exact := supportedSectionsSC_exact Y hY F
  epi_g := by
    dsimp [supportedSectionsSC]
    exact TopCat.Presheaf.IsFlasque.epi _

/-- A global section restricts to zero on `X \ Y` exactly when its support lies in `Y`. -/
theorem restrict_closedComplement_eq_zero_iff (Y : Set X) (hY : IsClosed Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (s : F.obj.obj (op ⊤)) :
    F.obj.map (homOfLE (le_top : closedComplement Y hY ≤ ⊤)).op s = 0 ↔
      Subtype.val '' sectionSupport F ⊤ s ⊆ Y := by
  constructor
  · rintro h - ⟨x, hx, rfl⟩
    by_contra hxY
    apply hx
    rw [← F.presheaf.germ_res_apply (homOfLE (le_top : closedComplement Y hY ≤ ⊤)) x.1 hxY s]
    erw [h]
    exact map_zero _
  · intro h
    apply TopCat.Presheaf.section_ext F
    intro x hx
    rw [map_zero, F.presheaf.germ_res_apply]
    by_contra hne
    exact hx (h ⟨⟨x, trivial⟩, hne, rfl⟩)

/-- **II.1.20.** The global sections in `Γ_Y(X,F)` are exactly the sections of `F` whose support
lies in `Y`. -/
theorem mem_range_supportedSections_iff (Y : Set X) (hY : IsClosed Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (s : F.obj.obj (op ⊤)) :
    s ∈ Set.range ((kernel.ι (restrictGlobalSections (closedComplement Y hY))).app F) ↔
      Subtype.val '' sectionSupport F ⊤ s ⊆ Y := by
  rw [← restrict_closedComplement_eq_zero_iff Y hY F s]
  have h := (ShortComplex.ab_exact_iff _).1 (supportedSectionsSC_exact Y hY F)
  constructor
  · rintro ⟨t, rfl⟩
    exact congrArg (fun φ => φ t) ((supportedSectionsSC Y hY F).zero) |>.trans rfl
  · intro hs
    exact h s hs

/-- In a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of abelian sheaves with `F'` flasque,
`Γ_Y(X,F) ⟶ Γ_Y(X,F'')` is surjective. -/
theorem supportedSections_map_epi_of_shortExact (Y : Set X) (hY : IsClosed Y)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) [S.X₁.IsFlasque] :
    Epi ((supportedSections Y hY).map S.g) := by
  set U := closedComplement Y hY
  set τ := restrictGlobalSections U
  let ι : ∀ F : TopCat.Sheaf AddCommGrpCat.{u} X,
      (supportedSections Y hY).obj F ⟶ (sheafSectionsOver ⊤).obj F := fun F => (kernel.ι τ).app F
  have hιinj : ∀ F, Function.Injective (ι F) := fun F =>
    (AddCommGrpCat.mono_iff_injective _).1 (supportedSectionsSC_mono_f Y hY F)
  have hexact : ∀ F (t : F.obj.obj (op ⊤)), τ.app F t = 0 → ∃ b, ι F b = t := fun F t ht =>
    (ShortComplex.ab_exact_iff _).1 (supportedSectionsSC_exact Y hY F) t ht
  have hnat : ∀ b, ι S.X₃ ((supportedSections Y hY).map S.g b) = S.g.hom.app (op ⊤) (ι S.X₂ b) :=
    fun b => congrArg (fun φ => φ b) ((kernel.ι τ).naturality S.g)
  have hτ : ∀ {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G) (t : F.obj.obj (op ⊤)),
      τ.app G (φ.hom.app (op ⊤) t) = φ.hom.app (op U) (τ.app F t) := fun φ t => by
    simp only [τ, restrictGlobalSections_app]
    exact (NatTrans.naturality_apply φ.hom _ t).symm
  rw [AddCommGrpCat.epi_iff_surjective]
  intro a
  have hg : Epi (S.g.hom.app (op ⊤)) := TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).1 hg (ι S.X₃ a)
  have hz : S.g.hom.app (op U) (τ.app S.X₂ t) = 0 := by
    rw [← hτ, ht]
    exact congrArg (fun φ => φ a) (kernel.condition τ |> congrArg (fun ψ => ψ.app S.X₃))
  obtain ⟨r, hr⟩ := TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f _ hz
  obtain ⟨r', hr'⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (TopCat.Presheaf.IsFlasque.epi (F := S.X₁.obj) (homOfLE (le_top : U ≤ ⊤)).op) r
  obtain ⟨b, hb⟩ := hexact S.X₂ (t - S.f.hom.app (op ⊤) r') (by
    have e1 : τ.app S.X₂ (t - S.f.hom.app (op ⊤) r') =
        τ.app S.X₂ t - τ.app S.X₂ (S.f.hom.app (op ⊤) r') := map_sub _ _ _
    rw [e1, hτ]
    change _ - S.f.hom.app (op U) (S.X₁.obj.map (homOfLE le_top).op r') = 0
    rw [hr', hr]
    exact sub_self _)
  refine ⟨b, hιinj _ ?_⟩
  have e2 : S.g.hom.app (op ⊤) (t - S.f.hom.app (op ⊤) r') =
      S.g.hom.app (op ⊤) t - S.g.hom.app (op ⊤) (S.f.hom.app (op ⊤) r') := map_sub _ _ _
  rw [hnat, hb, e2, ht]
  have : S.g.hom.app (op ⊤) (S.f.hom.app (op ⊤) r') = 0 := by
    have h0 := congrArg (fun φ => φ.hom.app (op ⊤) r') S.zero
    exact h0
  rw [this]
  exact sub_zero _

end Supports

section LocalizationSequence

variable {X : TopCat.{u}}

/-- Restriction of abelian sheaves to an open subset `V`: `F|_V (W) = F(W)`. -/
noncomputable abbrev openRestrict (V : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ (TopCat.of V).Sheaf AddCommGrpCat.{u} :=
  V.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}

/-- Extension by zero is left adjoint to restriction to an open subset. -/
noncomputable def openRestrictAdjunction (V : Opens X) :
    openExtensionByZeroFunctor V ⊣ openRestrict V :=
  (openExtensionByZeroAdjunction V).ofNatIsoRight
    (V.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u})

/-- Extension by zero preserves monomorphisms. -/
instance openExtensionByZeroFunctor_preservesMonomorphisms (V : Opens X) :
    (openExtensionByZeroFunctor V).PreservesMonomorphisms := by
  have hZ : (openZeroFunctor V).PreservesMonomorphisms := ⟨fun {F G} φ hφ => by
    have : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of V)) :=
      inferInstance
    have : (TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of V)).PreservesMonomorphisms :=
      CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
    have h1 : Mono ((TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of V)).map φ) :=
      @Functor.map_mono _ _ _ _ _ _ _ _ φ hφ
    have h1' : ∀ W',
        Mono (((TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of V)).map φ).app W') :=
      fun W' => inferInstance
    have h2 : ∀ W, Mono (((openZeroFunctor V).map φ).app W) := fun W => by
      rw [AddCommGrpCat.mono_iff_injective]
      intro s t h
      apply Subtype.ext
      exact (AddCommGrpCat.mono_iff_injective _).1 (h1' _) (congrArg Subtype.val h)
    exact NatTrans.mono_of_mono_app _⟩
  have : PreservesFiniteLimits
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  have hP :
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  exact @Functor.preservesMonomorphisms_comp _ _ _ _ _ _ (openZeroFunctor V)
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hZ hP

/-- Restriction to an open subset preserves injective abelian sheaves. -/
theorem injective_openRestrict_obj (V : Opens X) (I : X.Sheaf AddCommGrpCat.{u})
    [Injective I] : Injective ((openRestrict V).obj I) :=
  (openRestrictAdjunction V).map_injective I inferInstance

instance openRestrict_preservesFiniteLimits (V : Opens X) :
    PreservesFiniteLimits (openRestrict V) := by
  have : PreservesLimitsOfSize.{u, u + 1} (openRestrict V) :=
    (openRestrictAdjunction V).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize.preservesFiniteLimits _

instance openRestrict_preservesFiniteColimits (V : Opens X) :
    PreservesFiniteColimits (openRestrict V) := by
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    V.inclusion').leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u + 1} (openRestrict V) :=
    @preservesColimits_of_natIso _ _ _ _ _ _
      (V.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}) h
  exact PreservesColimitsOfSize.preservesFiniteColimits _

instance openRestrict_additive (V : Opens X) : (openRestrict V).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Sections over an open subset are additive. -/
instance sheafSectionsOver_additive (V : Opens X) : (sheafSectionsOver V).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Global sections of the restriction `F|_V` are the sections of `F` over `V`. -/
noncomputable def openRestrictSectionsIso (V : Opens X) :
    openRestrict V ⋙ sheafSectionsOver (X := TopCat.of V) ⊤ ≅ sheafSectionsOver V :=
  NatIso.ofComponents
    (fun F => F.obj.mapIso (eqToIso (Opens.isOpenEmbedding_obj_top V).symm).op)
    (fun φ => (φ.hom.naturality _).symm)

/-- Restricting an injective resolution of `F` to an open subset `V` gives an injective resolution
of `F|_V`. -/
noncomputable abbrev openRestrictInjectiveResolution (V : Opens X) {F : X.Sheaf AddCommGrpCat.{u}}
    (I : InjectiveResolution F) : InjectiveResolution ((openRestrict V).obj F) where
  cocomplex := ((openRestrict V).mapHomologicalComplex _).obj I.cocomplex
  injective n := injective_openRestrict_obj V (I.cocomplex.X n)
  ι := (HomologicalComplex.singleMapHomologicalComplex (openRestrict V) _ 0).inv.app F ≫
    ((openRestrict V).mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

variable (Y : Set X) (hY : IsClosed Y)

/-- The inclusion `Γ_Y(X,-) ⟶ Γ(X,-)`. -/
noncomputable def supportedSectionsι : supportedSections Y hY ⟶ sheafSectionsOver ⊤ :=
  kernel.ι (restrictGlobalSections (closedComplement Y hY))

/-- The sequence `0 ⟶ Γ_Y(X,K) ⟶ Γ(X,K) ⟶ Γ(U,K)` applied degreewise to a complex `K` of sheaves,
where `U = X \ Y`. -/
noncomputable def localizationComplexSC (K : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (supportedSectionsι Y hY) _).app K)
    ((NatTrans.mapHomologicalComplex (restrictGlobalSections (closedComplement Y hY)) _).app K)
    (by
      ext n : 1
      exact (supportedSectionsSC Y hY (K.X n)).zero)

/-- For a complex of injective sheaves the localization sequence of complexes is short exact. -/
theorem localizationComplexSC_shortExact (K : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ)
    [∀ n, Injective (K.X n)] : (localizationComplexSC Y hY K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    have := injectiveAbelianSheaf_isFlasque (K.X n)
    exact supportedSectionsSC_shortExact_of_isFlasque Y hY (K.X n)

section Restriction

instance sheafSectionsOver_top_additive (V : Opens X) :
    (sheafSectionsOver (X := TopCat.of V) ⊤).Additive :=
  sheafSectionsOver_additive _

variable (V : Opens X)

/-- The comparison `I'.ι ≫ φ' = single₀(f|_V) ≫ J'.ι` for restricted resolutions. -/
lemma openRestrictInjectiveResolution_comm {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    (openRestrictInjectiveResolution V I).ι.f 0 ≫
        (((openRestrict V).mapHomologicalComplex _).map φ).f 0 =
      (openRestrict V).map f ≫ (openRestrictInjectiveResolution V J).ι.f 0 := by
  have h : I.ι ≫ φ = (CochainComplex.single₀ _).map f ≫ J.ι := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    rcases n with _ | n
    · simpa using comm
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _
  have h' := congrArg
    (fun ψ => ((openRestrict V).mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) h
  simp only [Functor.map_comp] at h'
  have h'' := (HomologicalComplex.singleMapHomologicalComplex (openRestrict V)
    (ComplexShape.up ℕ) 0).inv.naturality f
  have key : (openRestrictInjectiveResolution V I).ι ≫
      ((openRestrict V).mapHomologicalComplex _).map φ =
      (CochainComplex.single₀ _).map ((openRestrict V).map f) ≫
        (openRestrictInjectiveResolution V J).ι := by
    dsimp only [openRestrictInjectiveResolution]
    rw [Category.assoc, h', ← Category.assoc, ← Category.assoc]
    congr 1
    exact h''.symm
  refine (HomologicalComplex.congr_hom key 0).trans ?_
  exact (HomologicalComplex.comp_f _ _ 0).trans (by rw [CochainComplex.single₀_map_f_zero]; rfl)

/-- `H^n(V, F|_V)` computed from `Γ(V, I)` for an injective resolution `I` of `F`. -/
noncomputable def openRestrictCohomologyIso {F : X.Sheaf AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (n : ℕ) :
    ((sheafSectionsOver (X := TopCat.of V) ⊤).rightDerived n).obj ((openRestrict V).obj F) ≅
      (HomologicalComplex.homologyFunctor _ _ n).obj
        (((sheafSectionsOver V).mapHomologicalComplex _).obj I.cocomplex) :=
  (openRestrictInjectiveResolution V I).isoRightDerivedObj _ n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso (openRestrictSectionsIso V) _).app I.cocomplex)

@[reassoc]
lemma openRestrictCohomologyIso_hom_naturality {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    ((sheafSectionsOver (X := TopCat.of V) ⊤).rightDerived n).map ((openRestrict V).map f) ≫
        (openRestrictCohomologyIso V J n).hom =
      (openRestrictCohomologyIso V I n).hom ≫
        (HomologicalComplex.homologyFunctor _ _ n).map
          (((sheafSectionsOver V).mapHomologicalComplex _).map φ) := by
  simp only [openRestrictCohomologyIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc ((openRestrict V).map f)
    (openRestrictInjectiveResolution V I) (openRestrictInjectiveResolution V J)
    (((openRestrict V).mapHomologicalComplex _).map φ)
    (openRestrictInjectiveResolution_comm V f I J φ comm)]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact ((Functor.mapHomologicalComplexCompIso (openRestrictSectionsIso V) _).hom.naturality φ)

/-- `R^nΓ(V,-)(F) ≅ H^n(V, F|_V)`, where `Γ(V,-)` is taken on sheaves on `X`. -/
noncomputable def sectionsOverRightDerivedIso (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    ((sheafSectionsOver V).rightDerived n).obj F ≅
      ((sheafSectionsOver (X := TopCat.of V) ⊤).rightDerived n).obj ((openRestrict V).obj F) :=
  (injectiveResolution F).isoRightDerivedObj _ n ≪≫
    (openRestrictCohomologyIso V (injectiveResolution F) n).symm

lemma sectionsOverRightDerivedIso_naturality {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (n : ℕ) :
    ((sheafSectionsOver V).rightDerived n).map f ≫ (sectionsOverRightDerivedIso V G n).hom =
      (sectionsOverRightDerivedIso V F n).hom ≫
        ((sheafSectionsOver (X := TopCat.of V) ⊤).rightDerived n).map ((openRestrict V).map f) := by
  let φ := InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)
  have comm := InjectiveResolution.desc_commutes_zero f (injectiveResolution G)
    (injectiveResolution F)
  simp only [sectionsOverRightDerivedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc f _ _ φ comm]
  rw [← cancel_mono (openRestrictCohomologyIso V (injectiveResolution G) n).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    openRestrictCohomologyIso_hom_naturality V f _ _ φ comm, Iso.inv_hom_id_assoc]

/-- The restriction map `H^n(X,F) ⟶ H^n(V,F|_V)`, natural in `F`. -/
noncomputable def cohomologyRestriction (n : ℕ) :
    (sheafSectionsOver (X := X) ⊤).rightDerived n ⟶
      openRestrict V ⋙ (sheafSectionsOver (X := TopCat.of V) ⊤).rightDerived n :=
  NatTrans.rightDerived (restrictGlobalSections V) n ≫
    { app := fun F => (sectionsOverRightDerivedIso V F n).hom
      naturality := fun _ _ f => sectionsOverRightDerivedIso_naturality V f n }

end Restriction


section Localization

/-- The map `H^n_Y(X,F) ⟶ H^n(X,F)` induced by `Γ_Y(X,-) ⟶ Γ(X,-)`, natural in `F`. -/
noncomputable def cohomologyWithSupportsToCohomology (n : ℕ) :
    cohomologyWithSupports Y hY n ⟶ (sheafSectionsOver (X := X) ⊤).rightDerived n :=
  NatTrans.rightDerived (supportedSectionsι Y hY) n

variable {Y hY} in
/-- `H^n_Y(X,F)` computed from `Γ_Y(X,I)` for an injective resolution `I` of `F`. -/
noncomputable def localizationIso₁ {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (n : ℕ) :
    (cohomologyWithSupports Y hY n).obj F ≅
      (localizationComplexSC Y hY I.cocomplex).X₁.homology n :=
  I.isoRightDerivedObj (supportedSections Y hY) n

variable {Y hY} in
/-- `H^n(X,F)` computed from `Γ(X,I)` for an injective resolution `I` of `F`. -/
noncomputable def localizationIso₂ {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (n : ℕ) :
    ((sheafSectionsOver (X := X) ⊤).rightDerived n).obj F ≅
      (localizationComplexSC Y hY I.cocomplex).X₂.homology n :=
  I.isoRightDerivedObj (sheafSectionsOver ⊤) n

variable {Y hY} in
/-- `H^n(U,F|_U)`, `U = X \ Y`, computed from `Γ(U,I)` for an injective resolution `I` of `F`. -/
noncomputable def localizationIso₃ {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (n : ℕ) :
    ((sheafSectionsOver (X := TopCat.of (closedComplement Y hY)) ⊤).rightDerived n).obj
        ((openRestrict (closedComplement Y hY)).obj F) ≅
      (localizationComplexSC Y hY I.cocomplex).X₃.homology n :=
  openRestrictCohomologyIso (closedComplement Y hY) I n

lemma cohomologyWithSupportsToCohomology_app_eq {F : X.Sheaf AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (n : ℕ) :
    (cohomologyWithSupportsToCohomology Y hY n).app F =
      (localizationIso₁ I n).hom ≫
        HomologicalComplex.homologyMap (localizationComplexSC Y hY I.cocomplex).f n ≫
        (localizationIso₂ I n).inv :=
  InjectiveResolution.rightDerived_app_eq _ I n

lemma cohomologyRestriction_app_eq (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (cohomologyRestriction (closedComplement Y hY) n).app F =
      (localizationIso₂ (injectiveResolution F) n).hom ≫
        HomologicalComplex.homologyMap
          (localizationComplexSC Y hY (injectiveResolution F).cocomplex).g n ≫
        (localizationIso₃ (injectiveResolution F) n).inv := by
  simp only [cohomologyRestriction, NatTrans.comp_app,
    InjectiveResolution.rightDerived_app_eq _ (injectiveResolution F), sectionsOverRightDerivedIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The morphism of localization sequences of complexes induced by a cochain map. -/
noncomputable def localizationComplexSCMap {K L : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ}
    (φ : K ⟶ L) : localizationComplexSC Y hY K ⟶ localizationComplexSC Y hY L where
  τ₁ := ((supportedSections Y hY).mapHomologicalComplex _).map φ
  τ₂ := ((sheafSectionsOver (X := X) ⊤).mapHomologicalComplex _).map φ
  τ₃ := ((sheafSectionsOver (closedComplement Y hY)).mapHomologicalComplex _).map φ
  comm₁₂ := NatTrans.mapHomologicalComplex_naturality _ _
  comm₂₃ := NatTrans.mapHomologicalComplex_naturality _ _

@[reassoc]
lemma localizationIso₁_inv_naturality {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    (localizationIso₁ (Y := Y) (hY := hY) I n).inv ≫ (cohomologyWithSupports Y hY n).map f =
      HomologicalComplex.homologyMap (localizationComplexSCMap Y hY φ).τ₁ n ≫
        (localizationIso₁ J n).inv :=
  InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ comm _ n

@[reassoc]
lemma localizationIso₃_hom_naturality {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    ((sheafSectionsOver (X := TopCat.of (closedComplement Y hY)) ⊤).rightDerived n).map
        ((openRestrict (closedComplement Y hY)).map f) ≫ (localizationIso₃ J n).hom =
      (localizationIso₃ (Y := Y) (hY := hY) I n).hom ≫
        HomologicalComplex.homologyMap (localizationComplexSCMap Y hY φ).τ₃ n :=
  openRestrictCohomologyIso_hom_naturality _ f I J φ comm n

/-- The connecting morphism `H^n(U,F|_U) ⟶ H^{n+1}_Y(X,F)`, `U = X \ Y`, of the localization
sequence, computed from the injective resolution of `F` chosen by `injectiveResolution`. -/
noncomputable def localizationδApp (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    ((sheafSectionsOver (X := TopCat.of (closedComplement Y hY)) ⊤).rightDerived n).obj
        ((openRestrict (closedComplement Y hY)).obj F) ⟶
      (cohomologyWithSupports Y hY (n + 1)).obj F :=
  (localizationIso₃ (injectiveResolution F) n).hom ≫
    (localizationComplexSC_shortExact Y hY (injectiveResolution F).cocomplex).δ n (n + 1) (by simp) ≫
      (localizationIso₁ (injectiveResolution F) (n + 1)).inv

lemma localizationδApp_naturality {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ) :
    ((sheafSectionsOver (X := TopCat.of (closedComplement Y hY)) ⊤).rightDerived n).map
        ((openRestrict (closedComplement Y hY)).map f) ≫ localizationδApp Y hY G n =
      localizationδApp Y hY F n ≫ (cohomologyWithSupports Y hY (n + 1)).map f := by
  let φ := InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)
  have comm := InjectiveResolution.desc_commutes_zero f (injectiveResolution G)
    (injectiveResolution F)
  have hδ := HomologicalComplex.HomologySequence.δ_naturality (localizationComplexSCMap Y hY φ)
    (localizationComplexSC_shortExact Y hY (injectiveResolution F).cocomplex)
    (localizationComplexSC_shortExact Y hY (injectiveResolution G).cocomplex) n (n + 1) (by simp)
  simp only [localizationδApp, Category.assoc]
  rw [localizationIso₃_hom_naturality_assoc Y hY f _ _ φ comm n,
    localizationIso₁_inv_naturality Y hY f _ _ φ comm (n + 1), reassoc_of% hδ]

/-- The connecting morphisms `H^n(U,F|_U) ⟶ H^{n+1}_Y(X,F)` of the localization sequence,
`U = X \ Y`, natural in `F`. -/
noncomputable def localizationδ (n : ℕ) :
    openRestrict (closedComplement Y hY) ⋙
        (sheafSectionsOver (X := TopCat.of (closedComplement Y hY)) ⊤).rightDerived n ⟶
      cohomologyWithSupports Y hY (n + 1) where
  app F := localizationδApp Y hY F n
  naturality _ _ f := localizationδApp_naturality Y hY f n

lemma localizationδ_app (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (localizationδ Y hY n).app F =
      (localizationIso₃ (injectiveResolution F) n).hom ≫
        (localizationComplexSC_shortExact Y hY (injectiveResolution F).cocomplex).δ n (n + 1) (by simp) ≫
          (localizationIso₁ (injectiveResolution F) (n + 1)).inv :=
  rfl

/-- The localization sequence starts with `0`: `H^0_Y(X,F) ⟶ H^0(X,F)` is injective. -/
theorem cohomologyWithSupportsToCohomology_mono (F : X.Sheaf AddCommGrpCat.{u}) :
    Mono ((cohomologyWithSupportsToCohomology Y hY 0).app F) := by
  rw [cohomologyWithSupportsToCohomology_app_eq Y hY (injectiveResolution F)]
  have : Mono ((localizationComplexSC Y hY (injectiveResolution F).cocomplex).f.f 0) :=
    supportedSectionsSC_mono_f Y hY _
  have := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    (localizationComplexSC Y hY (injectiveResolution F).cocomplex).f 0 (fun i => by simp)
  infer_instance

/-- Exactness of `H^n_Y(X,F) ⟶ H^n(X,F) ⟶ H^n(U,F|_U)`, `U = X \ Y`. -/
theorem localization_exact₂ (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (ShortComplex.mk ((cohomologyWithSupportsToCohomology Y hY n).app F)
      ((cohomologyRestriction (closedComplement Y hY) n).app F) (by
        rw [cohomologyWithSupportsToCohomology_app_eq Y hY (injectiveResolution F),
          cohomologyRestriction_app_eq]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← HomologicalComplex.homologyMap_comp_assoc, ShortComplex.zero,
          HomologicalComplex.homologyMap_zero, zero_comp, comp_zero])).Exact := by
  have hS := localizationComplexSC_shortExact Y hY (injectiveResolution F).cocomplex
  refine ShortComplex.exact_of_iso ?_ (hS.homology_exact₂ n)
  refine ShortComplex.isoMk (localizationIso₁ (injectiveResolution F) n).symm
    (localizationIso₂ (injectiveResolution F) n).symm
    (localizationIso₃ (injectiveResolution F) n).symm ?_ ?_
  · simp [cohomologyWithSupportsToCohomology_app_eq Y hY (injectiveResolution F)]
  · simp [cohomologyRestriction_app_eq]

/-- Exactness of `H^n(X,F) ⟶ H^n(U,F|_U) ⟶ H^{n+1}_Y(X,F)`, `U = X \ Y`. -/
theorem localization_exact₃ (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (ShortComplex.mk ((cohomologyRestriction (closedComplement Y hY) n).app F)
      ((localizationδ Y hY n).app F) (by
        rw [cohomologyRestriction_app_eq, localizationδ_app]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [ShortComplex.ShortExact.comp_δ_assoc, zero_comp, comp_zero])).Exact := by
  have hS := localizationComplexSC_shortExact Y hY (injectiveResolution F).cocomplex
  refine ShortComplex.exact_of_iso ?_ (hS.homology_exact₃ n (n + 1) (by simp))
  refine ShortComplex.isoMk (localizationIso₂ (injectiveResolution F) n).symm
    (localizationIso₃ (injectiveResolution F) n).symm
    (localizationIso₁ (injectiveResolution F) (n + 1)).symm ?_ ?_
  · simp [cohomologyRestriction_app_eq]
  · simp [localizationδ_app]

/-- Exactness of `H^n(U,F|_U) ⟶ H^{n+1}_Y(X,F) ⟶ H^{n+1}(X,F)`, `U = X \ Y`. -/
theorem localization_exact₁ (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (ShortComplex.mk ((localizationδ Y hY n).app F)
      ((cohomologyWithSupportsToCohomology Y hY (n + 1)).app F) (by
        rw [cohomologyWithSupportsToCohomology_app_eq Y hY (injectiveResolution F),
          localizationδ_app]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [ShortComplex.ShortExact.δ_comp_assoc, zero_comp, comp_zero])).Exact := by
  have hS := localizationComplexSC_shortExact Y hY (injectiveResolution F).cocomplex
  refine ShortComplex.exact_of_iso ?_ (hS.homology_exact₁ n (n + 1) (by simp))
  refine ShortComplex.isoMk (localizationIso₃ (injectiveResolution F) n).symm
    (localizationIso₁ (injectiveResolution F) (n + 1)).symm
    (localizationIso₂ (injectiveResolution F) (n + 1)).symm ?_ ?_
  · simp [localizationδ_app]
  · simp [cohomologyWithSupportsToCohomology_app_eq Y hY (injectiveResolution F)]

/-- Flasque sheaves are `Γ_Y(X,-)`-acyclic. -/
theorem isRightAcyclic_supportedSections_of_isFlasque (F : X.Sheaf AddCommGrpCat.{u})
    [F.IsFlasque] : IsRightAcyclic (supportedSections Y hY) F :=
  isRightAcyclic_of_shortExact_injective (supportedSections Y hY) (fun G => G.IsFlasque)
    (fun S hS h₁ h₂ => by
      have := h₁
      have := injectiveAbelianSheaf_isFlasque S.X₂
      exact ⟨TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS,
        supportedSections_map_epi_of_shortExact Y hY hS⟩) F inferInstance

end Localization

end LocalizationSequence

end Hartshorne
