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

/-!
# Cohomology with supports in a closed subset (partial)

Hartshorne, *Algebraic Geometry*, III, Exercise 2.3, p. 212.

For a closed subset `Y` of a topological space `X`, `Hartshorne.supportedSections Y hY` is the
functor `Γ_Y(X,-)` on abelian sheaves, the kernel of restriction `Γ(X,-) ⟶ Γ(X \ Y,-)`. Its
elements are exactly the global sections whose support lies in `Y`
(`Hartshorne.mem_range_supportedSections_iff`). It is left exact, and
`Hartshorne.cohomologyWithSupports Y hY n` is its `n`-th right derived functor `H^n_Y(X,-)`.

For a flasque sheaf `F` the sequence `0 ⟶ Γ_Y(X,F) ⟶ Γ(X,F) ⟶ Γ(X \ Y,F) ⟶ 0` is exact, and
in a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` with `F'` flasque the map
`Γ_Y(X,F) ⟶ Γ_Y(X,F'')` is surjective. The dimension-shifting lemma
`Hartshorne.isRightAcyclic_of_shortExact_injective` turns such surjectivity statements into
acyclicity.

The localization long exact sequence itself is not yet formalized here.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Hartshorne

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

end Hartshorne
