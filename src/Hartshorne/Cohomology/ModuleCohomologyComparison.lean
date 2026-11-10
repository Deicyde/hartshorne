/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AcyclicResolutionComparison
import Hartshorne.Cohomology.InjectiveModuleSheafFlasque
import Hartshorne.Cohomology.ModuleSheavesEnoughInjectives
import Hartshorne.Cohomology.SheafCohomologyFlasque

/-!
# Module and abelian-sheaf cohomology agree

Hartshorne, *Algebraic Geometry*, III, Proposition 2.6 and Remark 2.6.1 (p. 208).

Let `(X, 𝒪_X)` be a ringed space. The right derived functors of the global section functor
`Γ(X, -) : Mod(𝒪_X) ⟶ Ab`, computed with injective resolutions in the category of
`𝒪_X`-modules, are naturally isomorphic to the cohomology of the underlying abelian sheaf
(`Hartshorne.moduleSheafCohomologyIso`, `Hartshorne.moduleSheafCohomologyNatIso`).

Computing the derived functors of `Γ(X, -) : Mod(𝒪_X) ⟶ Mod(Γ(X, 𝒪_X))` instead gives the same
groups after forgetting the module structure (`Hartshorne.moduleSheafCohomologyModuleNatIso`),
which equips each `Hⁿ(X, M)` with a functorial `Γ(X, 𝒪_X)`-module structure (Remark 2.6.1).

## Proof

The functor from `𝒪_X`-modules to abelian sheaves is exact
(`Hartshorne.ModuleCohomology.toSheaf_preservesFiniteColimits`; it preserves finite limits by
Mathlib, and finite colimits because module sheafification computes the underlying abelian
sheafification). So an injective resolution `M ⟶ I^•` of `𝒪_X`-modules gives a resolution of the
underlying abelian sheaf, whose terms are flasque (injective module sheaves are flasque), hence
`Γ(X, -)`-acyclic. Acyclic resolutions compute derived functors.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Hartshorne

namespace ModuleCohomology

/-- Let `L ⊣ G` with invertible counit. If `L ⋙ T` preserves colimits of shape `K`, so does `T`. -/
theorem preservesColimitsOfShape_of_isIso_counit {C D E : Type*} [Category* C] [Category* D]
    [Category* E] {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) [IsIso adj.counit] (T : D ⥤ E)
    (K : Type*) [Category* K] [HasColimitsOfShape K C] [PreservesColimitsOfShape K L]
    [PreservesColimitsOfShape K (L ⋙ T)] : PreservesColimitsOfShape K T where
  preservesColimit {F} := by
    have : PreservesColimit (F ⋙ G ⋙ L) T :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit (F ⋙ G)))
        (isColimitOfPreserves (L ⋙ T) (colimit.isColimit (F ⋙ G)))
    exact preservesColimit_of_iso_diagram T
      (Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor)

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The underlying abelian sheaf of a module sheaf preserves finite colimits. -/
instance toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) where
  preservesFiniteColimits K _ _ := by
    have : PreservesColimitsOfShape K
        (PresheafOfModules.sheafification.{u} (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{u} R) :=
      preservesColimitsOfShape_of_natIso
        (PresheafOfModules.sheafificationCompToSheaf.{u} (𝟙 R.obj)).symm
    exact preservesColimitsOfShape_of_isIso_counit
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) _ K

/-- The `𝒪_X`-modules on a ringed space have enough injectives (Hartshorne III.2,
Proposition 2.2), for an arbitrary sheaf of rings `R`. `sheafOfModules_enoughInjectives`
(RingedSpace/SheafExt.lean) is the special case `R = ringCatSheafOf R'` of a sheaf of
commutative rings. -/
instance sheafOfModules_enoughInjectives_ringCat : EnoughInjectives (SheafOfModules.{u} R) :=
  moduleSheaves_enoughInjectives X R

/-- The underlying abelian sheaf of an `𝒪_X`-module, as a functor to the category of abelian
sheaves on `X` used by sheaf cohomology. -/
def toTopSheaf : SheafOfModules.{u} R ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf.{u} R

instance : (toTopSheaf R).Additive where
  map_add := rfl

instance : PreservesFiniteLimits (toTopSheaf R) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R))

instance : PreservesFiniteColimits (toTopSheaf R) :=
  toSheaf_preservesFiniteColimits R

/-- The global section functor `Γ(X, -) : Mod(𝒪_X) ⟶ Ab`. -/
abbrev moduleGlobalSections : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  toTopSheaf R ⋙ sheafSectionsOver (X := X) ⊤

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation from the underlying abelian sheaf of `M` to the underlying abelian sheaves
of the chosen injective resolution of `M` in `𝒪_X`-modules. -/
def augmentation (M : SheafOfModules.{u} R) :
    (CochainComplex.single₀ _).obj ((toTopSheaf R).obj M) ⟶
      ((toTopSheaf R).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution M).cocomplex :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(toTopSheaf R).map ((injectiveResolution M).ι.f 0), by
      rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp,
        InjectiveResolution.ι_f_zero_comp_complex_d, Functor.map_zero]⟩

@[simp]
theorem augmentation_f_zero (M : SheafOfModules.{u} R) :
    (augmentation R M).f 0 =
      (toTopSheaf R).map ((injectiveResolution M).ι.f 0) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation is a resolution, since passing to the underlying abelian sheaf is exact. -/
instance quasiIso_augmentation (M : SheafOfModules.{u} R) : QuasiIso (augmentation R M) := by
  rw [quasiIso_iff]
  intro n
  rcases n with _ | n
  · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · have hm : Mono ((augmentation R M).f 0) := by
        rw [augmentation_f_zero]
        exact Functor.map_mono _ _
      refine ⟨?_, hm⟩
      have hex := (injectiveResolution M).exact₀.map_of_mono_of_preservesKernel
        (toTopSheaf R) inferInstance inferInstance
      refine (ShortComplex.exact_iff_of_iso ?_).1 hex
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [augmentation_f_zero]) (by simp)
    all_goals first
      | rfl
      | exact HomologicalComplex.shape (((toTopSheaf R).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (injectiveResolution M).cocomplex) 0 0
            (fun h ↦ Nat.succ_ne_zero 0 h)
  · rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ n),
      HomologicalComplex.exactAt_iff]
    have h := (injectiveResolution M).cocomplex_exactAt_succ n
    rw [HomologicalComplex.exactAt_iff] at h
    exact h.map (toTopSheaf R)

/-- The underlying abelian sheaves of an injective resolution in `𝒪_X`-modules are flasque, hence
acyclic for `Γ(X, -)`. -/
theorem isRightAcyclic_toSheaf_injectiveResolution (M : SheafOfModules.{u} R) (i : ℕ) :
    IsRightAcyclic (sheafSectionsOver (X := X) ⊤)
      ((toTopSheaf R).obj ((injectiveResolution M).cocomplex.X i)) :=
  have : ((toTopSheaf R).obj ((injectiveResolution M).cocomplex.X i)).IsFlasque :=
    injectiveModuleSheaf_isFlasque R ((injectiveResolution M).cocomplex.X i)
  isRightAcyclic_sheafSectionsOver_top_of_isFlasque _

end ModuleCohomology

open ModuleCohomology

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The right derived functors `RⁿΓ(X, -)` of the global section functor
`Γ(X, -) : Mod(𝒪_X) ⟶ Ab`, computed with injective resolutions of `𝒪_X`-modules. -/
abbrev moduleSheafCohomology (n : ℕ) : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  (moduleGlobalSections R).rightDerived n

/-- **Module and abelian-sheaf cohomology agree** (Hartshorne III, Proposition 2.6). For an
`𝒪_X`-module `M`, the right derived functors of `Γ(X, -)` computed in `𝒪_X`-modules agree with
the cohomology of the underlying abelian sheaf: `RⁿΓ(X, M) ≅ Hⁿ(X, M)`. -/
def moduleSheafCohomologyIso (M : SheafOfModules.{u} R) (n : ℕ) :
    (moduleSheafCohomology R n).obj M ≅
      (sheafCohomology X n).obj ((toTopSheaf R).obj M) :=
  (injectiveResolution M).isoRightDerivedObj (moduleGlobalSections R) n ≪≫
    (acyclicResolutionIso (sheafSectionsOver (X := X) ⊤) (augmentation R M)
      (isRightAcyclic_toSheaf_injectiveResolution R M) n).symm

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphisms `RⁿΓ(X, M) ≅ Hⁿ(X, M)` are natural in the `𝒪_X`-module `M`. -/
theorem moduleSheafCohomologyIso_naturality {M N : SheafOfModules.{u} R} (g : M ⟶ N) (n : ℕ) :
    (moduleSheafCohomology R n).map g ≫ (moduleSheafCohomologyIso R N n).hom =
      (moduleSheafCohomologyIso R M n).hom ≫
        (sheafCohomology X n).map ((toTopSheaf R).map g) := by
  let φ := InjectiveResolution.desc g (injectiveResolution N) (injectiveResolution M)
  have comm : augmentation R M ≫
      ((toTopSheaf R).mapHomologicalComplex _).map φ =
        (CochainComplex.single₀ _).map ((toTopSheaf R).map g) ≫
          augmentation R N := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, augmentation_f_zero,
      augmentation_f_zero, CochainComplex.single₀_map_f_zero,
      Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, ← Functor.map_comp,
      InjectiveResolution.desc_commutes_zero]
  have e1 := acyclicResolutionIso_naturality (sheafSectionsOver (X := X) ⊤) (augmentation R M)
    (isRightAcyclic_toSheaf_injectiveResolution R M) (augmentation R N)
    (isRightAcyclic_toSheaf_injectiveResolution R N) ((toTopSheaf R).map g)
    (((toTopSheaf R).mapHomologicalComplex _).map φ) comm n
  have e2 := InjectiveResolution.isoRightDerivedObj_hom_naturality g (injectiveResolution M)
    (injectiveResolution N) φ (InjectiveResolution.desc_commutes_zero _ _ _)
    (moduleGlobalSections R) n
  simp only [moduleSheafCohomologyIso, Iso.trans_hom, Iso.symm_hom]
  rw [reassoc_of% e2]
  simp only [Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact e1.symm

/-- **Module and abelian-sheaf cohomology agree** (Hartshorne III, Proposition 2.6), as a natural
isomorphism of functors `Mod(𝒪_X) ⟶ Ab`: `RⁿΓ(X, -) ≅ Hⁿ(X, -) ∘ (underlying abelian sheaf)`. -/
def moduleSheafCohomologyNatIso (n : ℕ) :
    moduleSheafCohomology R n ≅ toTopSheaf R ⋙ sheafCohomology X n :=
  NatIso.ofComponents (fun M ↦ moduleSheafCohomologyIso R M n)
    (fun g ↦ moduleSheafCohomologyIso_naturality R g n)

namespace ModuleCohomology

/-- Sections over `X` of an `𝒪_X`-module, as a `Γ(X, 𝒪_X)`-module, form an additive functor. -/
instance evaluation_additive : (SheafOfModules.evaluation.{u} R (op ⊤)).Additive where
  map_add := rfl

end ModuleCohomology

/-- The right derived functors `RⁿΓ(X, -)` of the global section functor
`Γ(X, -) : Mod(𝒪_X) ⟶ Mod(Γ(X, 𝒪_X))`, computed with injective resolutions of `𝒪_X`-modules. -/
abbrev moduleSheafCohomologyModule (n : ℕ) :
    SheafOfModules.{u} R ⥤ ModuleCat.{u} (R.obj.obj (op ⊤)) :=
  (SheafOfModules.evaluation.{u} R (op ⊤)).rightDerived n

/-- Forgetting the `Γ(X, 𝒪_X)`-module structure of `RⁿΓ(X, M)` gives the right derived functor of
`Γ(X, -) : Mod(𝒪_X) ⟶ Ab`, since forgetting the module structure is exact. -/
def moduleSheafCohomologyForgetIso (M : SheafOfModules.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat.{u} (R.obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        ((moduleSheafCohomologyModule R n).obj M) ≅
      (moduleSheafCohomology R n).obj M :=
  (forget₂ (ModuleCat.{u} (R.obj.obj (op ⊤))) AddCommGrpCat.{u}).mapIso
      ((injectiveResolution M).isoRightDerivedObj (SheafOfModules.evaluation.{u} R (op ⊤)) n) ≪≫
    (((((SheafOfModules.evaluation.{u} R (op ⊤)).mapHomologicalComplex _).obj
      (injectiveResolution M).cocomplex).sc n).mapHomologyIso
        (forget₂ (ModuleCat.{u} (R.obj.obj (op ⊤))) AddCommGrpCat.{u})).symm ≪≫
    ((injectiveResolution M).isoRightDerivedObj (moduleGlobalSections R) n).symm

set_option backward.isDefEq.respectTransparency false in
theorem moduleSheafCohomologyForgetIso_naturality {M N : SheafOfModules.{u} R} (g : M ⟶ N)
    (n : ℕ) :
    (forget₂ (ModuleCat.{u} (R.obj.obj (op ⊤))) AddCommGrpCat.{u}).map
        ((moduleSheafCohomologyModule R n).map g) ≫ (moduleSheafCohomologyForgetIso R N n).hom =
      (moduleSheafCohomologyForgetIso R M n).hom ≫ (moduleSheafCohomology R n).map g := by
  let φ := InjectiveResolution.desc g (injectiveResolution N) (injectiveResolution M)
  have e1 := InjectiveResolution.isoRightDerivedObj_hom_naturality g (injectiveResolution M)
    (injectiveResolution N) φ (InjectiveResolution.desc_commutes_zero _ _ _)
    (SheafOfModules.evaluation.{u} R (op ⊤)) n
  have e2 := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (((SheafOfModules.evaluation.{u} R (op ⊤)).mapHomologicalComplex _).map φ))
    (forget₂ (ModuleCat.{u} (R.obj.obj (op ⊤))) AddCommGrpCat.{u})
  have e3 := InjectiveResolution.isoRightDerivedObj_inv_naturality g (injectiveResolution M)
    (injectiveResolution N) φ (InjectiveResolution.desc_commutes_zero _ _ _)
    (moduleGlobalSections R) n
  simp only [moduleSheafCohomologyForgetIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [← Functor.map_comp_assoc, e1, Functor.map_comp, Category.assoc]
  congr 1
  refine ((reassoc_of% e2) _).trans ?_
  exact congrArg (_ ≫ ·) e3.symm

/-- **The `Γ(X, 𝒪_X)`-module structure on cohomology** (Hartshorne III, Remark 2.6.1). The right
derived functors of `Γ(X, -) : Mod(𝒪_X) ⟶ Mod(Γ(X, 𝒪_X))` agree, after forgetting the module
structure, with the cohomology of the underlying abelian sheaf, naturally in the `𝒪_X`-module.
This equips each `Hⁿ(X, M)` with a functorial `Γ(X, 𝒪_X)`-module structure. -/
def moduleSheafCohomologyModuleNatIso (n : ℕ) :
    moduleSheafCohomologyModule R n ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op ⊤))) AddCommGrpCat.{u} ≅
      toTopSheaf R ⋙ sheafCohomology X n :=
  NatIso.ofComponents
    (fun M ↦ moduleSheafCohomologyForgetIso R M n ≪≫ moduleSheafCohomologyIso R M n)
    (fun g ↦ by
      simp only [Functor.comp_map, Iso.trans_hom]
      rw [reassoc_of% moduleSheafCohomologyForgetIso_naturality,
        moduleSheafCohomologyIso_naturality, Category.assoc])

end Hartshorne
