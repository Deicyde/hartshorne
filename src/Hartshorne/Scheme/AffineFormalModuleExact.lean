/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ModuleCohomologyComparison
import Hartshorne.Scheme.FormalCompletionModule
import Mathlib.Topology.Sheaves.Abelian

/-!
# Toward exactness of affine module completion

Hartshorne, *Algebraic Geometry*, II, Proposition 9.4(c) (pp. 195–196): for a Noetherian ring `A`
and an ideal `I`, the functor `M ↦ M^Δ` from finite `A`-modules to modules on `Spf_I(A)` is exact.
The proof checks exactness on stalks: on the basic opens `D(f) ∩ V(I)` the sections of `M^Δ` are
the completions of the `M_f`, completion is exact on finite modules, and stalks are filtered
colimits of sections over basic neighbourhoods.

This file contains the parts of that argument proved so far.

* `Hartshorne.sheaf_exact_of_isBasis_sections`,
  `Hartshorne.sheafOfModules_exact_of_isBasis_sections`: a complex of sheaves of abelian groups,
  or of sheaves of modules over a sheaf of rings, is exact once, over every open of a basis of the
  topology, sections in the kernel of the second map come from the first term. This is the stalk
  criterion (Hartshorne II, Exercise 1.2) specialised to a basis.
* Levelwise functoriality of the completion `F̂ = lim_n (F / I ^ (n + 1) F)|_Y`: a morphism
  `φ : F ⟶ G` of `𝒪_X`-modules induces `I ^ (n + 1) F ⟶ I ^ (n + 1) G`
  (`Hartshorne.QuasicoherentIdealSubsheaf.powSmulHom`), the maps of quotients
  `F / I ^ (n + 1) F ⟶ G / I ^ (n + 1) G`
  (`Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionQuotientHom`), compatible with the
  quotient transition maps, and the maps `(F / I ^ (n + 1) F)|_Y ⟶ (G / I ^ (n + 1) G)|_Y` of
  modules over the completed structure sheaf
  (`Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionObjHom`).
* Naturality of the transition maps
  (`Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionObjHom_comp_moduleCompletionMap`), the
  induced morphism of inverse systems (`moduleCompletionDiagramHom`), the completion of a morphism
  `F̂ ⟶ Ĝ` (`moduleCompletionHom`) and the completion functor `F ↦ F̂`
  (`Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionFunctor`).
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

section BasisExactness

/-- **Exactness from sections over a basis.** A complex `F₁ ⟶ F₂ ⟶ F₃` of sheaves of abelian
groups on a space `X` is exact as soon as, for every open `U` in a basis of the topology, every
section of `F₂` over `U` killed by `F₂ ⟶ F₃` comes from a section of `F₁` over `U`. This is checked
on stalks, which are filtered colimits of sections over the basic neighbourhoods. -/
theorem sheaf_exact_of_isBasis_sections {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (h : ∀ U ∈ B, ∀ x : ToType (((TopCat.Sheaf.forget _ X).obj S.X₂).obj (op U)),
      ((TopCat.Sheaf.forget _ X).map S.g).app (op U) x = 0 →
        ∃ y : ToType (((TopCat.Sheaf.forget _ X).obj S.X₁).obj (op U)), ((TopCat.Sheaf.forget _ X).map S.f).app (op U) y = x) :
    S.Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro p
  rw [ShortComplex.ab_exact_iff]
  intro t ht
  obtain ⟨U, hpU, s, rfl⟩ := ((TopCat.Sheaf.forget _ X).obj S.X₂).exists_germ_eq t
  obtain ⟨V, hVB, hpV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hpU
  rw [← ((TopCat.Sheaf.forget _ X).obj S.X₂).germ_res_apply (homOfLE hVU) p hpV] at ht ⊢
  set s' := ((TopCat.Sheaf.forget _ X).obj S.X₂).map (homOfLE hVU).op s
  change (TopCat.Presheaf.stalkFunctor _ p).map ((TopCat.Sheaf.forget _ X).map S.g)
    (((TopCat.Sheaf.forget _ X).obj S.X₂).germ V p hpV s') = 0 at ht
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ht
  obtain ⟨W, hpW, iW, iV, hW⟩ := ((TopCat.Sheaf.forget _ X).obj S.X₃).germ_eq p hpV hpV _ 0 (ht.trans (map_zero _).symm)
  obtain ⟨W', hW'B, hpW', hW'W⟩ := (Opens.isBasis_iff_nbhd.mp hB) hpW
  have hzero : ((TopCat.Sheaf.forget _ X).map S.g).app (op W')
      (((TopCat.Sheaf.forget _ X).obj S.X₂).map (homOfLE (hW'W.trans iW.le)).op s') = 0 := by
    rw [← ConcreteCategory.comp_apply, ((TopCat.Sheaf.forget _ X).map S.g).naturality,
      ConcreteCategory.comp_apply]
    have : (homOfLE (hW'W.trans iW.le)).op = iW.op ≫ (homOfLE hW'W).op := rfl
    rw [this, Functor.map_comp, ConcreteCategory.comp_apply, hW, map_zero, map_zero]
  obtain ⟨y, hy⟩ := h W' hW'B _ hzero
  refine ⟨((TopCat.Sheaf.forget _ X).obj S.X₁).germ W' p hpW' y, ?_⟩
  change (TopCat.Presheaf.stalkFunctor _ p).map ((TopCat.Sheaf.forget _ X).map S.f)
    (((TopCat.Sheaf.forget _ X).obj S.X₁).germ W' p hpW' y) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [hy]
  exact ((TopCat.Sheaf.forget _ X).obj S.X₂).germ_res_apply _ p hpW' s'

/-- **Exactness of sheaves of modules from sections over a basis.** A complex `M₁ ⟶ M₂ ⟶ M₃` of
sheaves of modules over a sheaf of rings on `X` is exact as soon as, for every open `U` in a basis
of the topology, every section of `M₂` over `U` killed by `M₂ ⟶ M₃` comes from a section of `M₁`
over `U`. -/
theorem sheafOfModules_exact_of_isBasis_sections {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (S : ShortComplex (SheafOfModules.{u} R))
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (h : ∀ U ∈ B, ∀ x : S.X₂.val.obj (op U), (S.g.val.app (op U)).hom x = 0 →
      ∃ y : S.X₁.val.obj (op U), (S.f.val.app (op U)).hom y = x) :
    S.Exact := by
  have : (ModuleCohomology.toTopSheaf R).Faithful :=
    inferInstanceAs (SheafOfModules.toSheaf.{u} R).Faithful
  rw [← ShortComplex.exact_map_iff_of_faithful S (ModuleCohomology.toTopSheaf R)]
  exact sheaf_exact_of_isBasis_sections _ hB (fun U hU x hx => h U hU x hx)

end BasisExactness

namespace QuasicoherentIdealSubsheaf

open ArtinReesKernelSheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

section Functoriality

variable {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H)

/-- A morphism of `𝒪_X`-modules sends sections of `I ^ k F` to sections of `I ^ k G`. -/
private lemma app_mem_powSmul (k : ℕ) {U : X.Opens} {s : Γ(F, U)}
    (hs : s ∈ sub (powSmul (quasicoherentIdealSubsheafEquiv I) k (⊤ : F.val.Submodule)) U) :
    φ.app U s ∈
      sub (powSmul (quasicoherentIdealSubsheafEquiv I) k (⊤ : G.val.Submodule)) U := by
  intro x hx
  obtain ⟨V, hVU, hxV, hV⟩ := hs x hx
  refine ⟨V, hVU, hxV, ?_⟩
  have hnat : res G hVU (φ.app U s) = φ.app V (res F hVU s) :=
    (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hVU).op) s).symm
  rw [hnat]
  let g : Γ(F, V) →ₗ[Γ(X, V)] Γ(G, V) :=
    { toFun := φ.app V, map_add' := map_add _, map_smul' := Scheme.Modules.Hom.app_smul φ }
  exact pow_smul_map_mem (RingHom.id _) g (P' := sub (⊤ : G.val.Submodule) V) (by rw [Ideal.map_id])
    (fun _ _ => trivial) k hV

/-- The map `I ^ (n + 1) F ⟶ I ^ (n + 1) G` induced by a morphism `F ⟶ G`. -/
def powSmulHom (n : ℕ) :
    ArtinReesKernelSheaf.toModules
        (powSmul (quasicoherentIdealSubsheafEquiv I) (n + 1) (⊤ : F.val.Submodule))
        (isLocal_powSmul _ _ _) ⟶
      ArtinReesKernelSheaf.toModules (powSmul (quasicoherentIdealSubsheafEquiv I) (n + 1) (⊤ : G.val.Submodule))
        (isLocal_powSmul _ _ _) :=
  ⟨{ app V := ModuleCat.ofHom ((φ.val.app V).hom.restrict
        (fun _ hs => I.app_mem_powSmul φ (n + 1) (U := V.unop) hs))
     naturality {V W} f := by
        ext x
        exact Subtype.ext (congrArg (fun g => g.hom x.1) (φ.val.naturality f)) }⟩

lemma powSmulHom_comp_powSmulι (n : ℕ) :
    I.powSmulHom φ n ≫ I.powSmulι G n = I.powSmulι F n ≫ φ :=
  rfl

/-- The map `F / I ^ (n + 1) F ⟶ G / I ^ (n + 1) G` induced by a morphism `F ⟶ G`. -/
def moduleCompletionQuotientHom (n : ℕ) :
    I.moduleCompletionQuotient F n ⟶ I.moduleCompletionQuotient G n :=
  cokernel.map _ _ (I.powSmulHom φ n) φ (I.powSmulHom_comp_powSmulι φ n)

lemma π_moduleCompletionQuotientHom (n : ℕ) :
    cokernel.π (I.powSmulι F n) ≫ I.moduleCompletionQuotientHom φ n =
      φ ≫ cokernel.π (I.powSmulι G n) :=
  cokernel.π_desc _ _ _

lemma moduleCompletionQuotientHom_id (n : ℕ) :
    I.moduleCompletionQuotientHom (𝟙 F) n = 𝟙 _ :=
  by
    refine (cancel_epi (cokernel.π (I.powSmulι F n))).1 ?_
    rw [π_moduleCompletionQuotientHom]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

private lemma cokernel_map_comp' {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B A' B' A'' B'' : C} (f : A ⟶ B) (f' : A' ⟶ B') (f'' : A'' ⟶ B'') [HasCokernel f]
    [HasCokernel f'] [HasCokernel f''] (p : A ⟶ A') (q : B ⟶ B') (p' : A' ⟶ A'')
    (q' : B' ⟶ B'') (w : f ≫ q = p ≫ f') (w' : f' ≫ q' = p' ≫ f'')
    (w'' : f ≫ q ≫ q' = (p ≫ p') ≫ f'') :
    cokernel.map f f'' (p ≫ p') (q ≫ q') w'' =
      cokernel.map f f' p q w ≫ cokernel.map f' f'' p' q' w' := by
  ext; simp

private lemma cokernel_map_desc_π {C : Type*} [Category C] [HasZeroMorphisms C]
    {A₁ A₀ B A₁' A₀' B' : C} (f₁ : A₁ ⟶ B) (f₀ : A₀ ⟶ B) (f₁' : A₁' ⟶ B') (f₀' : A₀' ⟶ B')
    [HasCokernel f₁] [HasCokernel f₀] [HasCokernel f₁'] [HasCokernel f₀'] (q : B ⟶ B')
    (p₁ : A₁ ⟶ A₁') (p₀ : A₀ ⟶ A₀') (h₁ : f₁ ≫ q = p₁ ≫ f₁') (h₀ : f₀ ≫ q = p₀ ≫ f₀')
    (w : f₁ ≫ cokernel.π f₀ = 0) (w' : f₁' ≫ cokernel.π f₀' = 0) :
    cokernel.map f₁ f₁' p₁ q h₁ ≫ cokernel.desc f₁' (cokernel.π f₀') w' =
      cokernel.desc f₁ (cokernel.π f₀) w ≫ cokernel.map f₀ f₀' p₀ q h₀ := by
  ext; simp

lemma moduleCompletionQuotientHom_comp (n : ℕ) :
    I.moduleCompletionQuotientHom (φ ≫ ψ) n =
      I.moduleCompletionQuotientHom φ n ≫ I.moduleCompletionQuotientHom ψ n :=
  cokernel_map_comp' _ _ _ (I.powSmulHom φ n) φ (I.powSmulHom ψ n) ψ
    (I.powSmulHom_comp_powSmulι φ n) (I.powSmulHom_comp_powSmulι ψ n) rfl

lemma moduleCompletionQuotientHom_comp_moduleCompletionQuotientMap (n : ℕ) :
    I.moduleCompletionQuotientHom φ (n + 1) ≫ I.moduleCompletionQuotientMap G n =
      I.moduleCompletionQuotientMap F n ≫ I.moduleCompletionQuotientHom φ n :=
  by
    unfold moduleCompletionQuotientHom moduleCompletionQuotientMap
    exact cokernel_map_desc_π (I.powSmulι F (n + 1)) (I.powSmulι F n) (I.powSmulι G (n + 1))
      (I.powSmulι G n) φ (I.powSmulHom φ (n + 1)) (I.powSmulHom φ n)
      (I.powSmulHom_comp_powSmulι φ (n + 1)) (I.powSmulHom_comp_powSmulι φ n) _ _

/-- The map `(F / I ^ (n + 1) F)|_Y ⟶ (G / I ^ (n + 1) G)|_Y` of `𝒪_{X̂_Y}`-modules induced by a
morphism `F ⟶ G`. -/
def moduleCompletionObjHom (n : ℕ) : I.moduleCompletionObj F n ⟶ I.moduleCompletionObj G n :=
  (SheafOfModules.pushforward.{u} (I.formalCompletionRingCatSheafπ n)).map
    ((Scheme.Modules.pullback (I.infinitesimalNeighborhoodι (n + 1))).map
      (I.moduleCompletionQuotientHom φ n))

lemma moduleCompletionObjHom_id (n : ℕ) : I.moduleCompletionObjHom (𝟙 F) n = 𝟙 _ := by
  simp [moduleCompletionObjHom, moduleCompletionQuotientHom_id]; rfl

lemma moduleCompletionObjHom_comp (n : ℕ) :
    I.moduleCompletionObjHom (φ ≫ ψ) n =
      I.moduleCompletionObjHom φ n ≫ I.moduleCompletionObjHom ψ n := by
  simp only [moduleCompletionObjHom]
  rw [moduleCompletionQuotientHom_comp, Functor.map_comp]
  exact Functor.map_comp _ _ _

/-- **Naturality of the transition maps** of the completion: the maps
`(F / I ^ (n + 1) F)|_Y ⟶ (G / I ^ (n + 1) G)|_Y` induced by `φ : F ⟶ G` commute with the
transition maps. -/
@[reassoc]
lemma moduleCompletionObjHom_comp_moduleCompletionMap (n : ℕ) :
    I.moduleCompletionObjHom φ (n + 1) ≫ I.moduleCompletionMap G n =
      I.moduleCompletionMap F n ≫ I.moduleCompletionObjHom φ n := by
  rw [moduleCompletionMap_eq, moduleCompletionMap_eq]
  exact pullbackUnitTransitionRestrict_naturality (I.infinitesimalNeighborhoodSucc n)
    (I.infinitesimalNeighborhoodι (n + 1 + 1)) (I.infinitesimalNeighborhoodι (n + 1))
    (Scheme.IdealSheafData.inclusion_subschemeι _)
    (I.functorToPreimageInfinitesimalNeighborhoodSucc n)
    (I.formalCompletionRingCatSheafπ (n + 1)) (I.formalCompletionRingCatSheafπ n)
    (fun V r => I.formalCompletionSheafMap_limit_π_apply n V.unop r)
    (I.moduleCompletionQuotientMap F n) (I.moduleCompletionQuotientMap G n)
    (I.moduleCompletionQuotientHom φ (n + 1)) (I.moduleCompletionQuotientHom φ n)
    (I.moduleCompletionQuotientHom_comp_moduleCompletionQuotientMap φ n).symm

/-- The morphism of inverse systems `(F / I ^ (n + 1) F)|_Y ⟶ (G / I ^ (n + 1) G)|_Y` induced by
`φ : F ⟶ G`. -/
def moduleCompletionDiagramHom : I.moduleCompletionDiagram F ⟶ I.moduleCompletionDiagram G :=
  NatTrans.ofOpSequence (fun n => I.moduleCompletionObjHom φ n) (fun n => by
    simp only [moduleCompletionDiagram, Functor.ofOpSequence_map_homOfLE_succ]
    exact (I.moduleCompletionObjHom_comp_moduleCompletionMap φ n).symm)

@[simp]
lemma moduleCompletionDiagramHom_app (n : ℕ) :
    (I.moduleCompletionDiagramHom φ).app (op n) = I.moduleCompletionObjHom φ n :=
  rfl

/-- **The completion of a morphism**: `φ : F ⟶ G` induces `F̂ ⟶ Ĝ`, the limit of the maps
`(F / I ^ (n + 1) F)|_Y ⟶ (G / I ^ (n + 1) G)|_Y`. -/
def moduleCompletionHom : I.moduleCompletion F ⟶ I.moduleCompletion G :=
  limMap (I.moduleCompletionDiagramHom φ)

@[reassoc (attr := simp)]
lemma moduleCompletionHom_π (n : ℕ) :
    I.moduleCompletionHom φ ≫ I.moduleCompletionπ G n =
      I.moduleCompletionπ F n ≫ I.moduleCompletionObjHom φ n :=
  limMap_π _ _

lemma moduleCompletionDiagramHom_id :
    I.moduleCompletionDiagramHom (𝟙 F) = 𝟙 (I.moduleCompletionDiagram F) := by
  ext ⟨n⟩ : 2
  exact I.moduleCompletionObjHom_id n

lemma moduleCompletionDiagramHom_comp :
    I.moduleCompletionDiagramHom (φ ≫ ψ) =
      I.moduleCompletionDiagramHom φ ≫ I.moduleCompletionDiagramHom ψ := by
  ext ⟨n⟩ : 2
  exact I.moduleCompletionObjHom_comp φ ψ n

lemma moduleCompletionHom_id : I.moduleCompletionHom (𝟙 F) = 𝟙 (I.moduleCompletion F) := by
  refine limit.hom_ext fun ⟨n⟩ => ?_
  change I.moduleCompletionHom (𝟙 F) ≫ I.moduleCompletionπ F n = 𝟙 _ ≫ I.moduleCompletionπ F n
  rw [moduleCompletionHom_π, moduleCompletionObjHom_id, Category.comp_id, Category.id_comp]

lemma moduleCompletionHom_comp :
    I.moduleCompletionHom (φ ≫ ψ) = I.moduleCompletionHom φ ≫ I.moduleCompletionHom ψ := by
  refine limit.hom_ext fun ⟨n⟩ => ?_
  change I.moduleCompletionHom (φ ≫ ψ) ≫ I.moduleCompletionπ H n =
    (I.moduleCompletionHom φ ≫ I.moduleCompletionHom ψ) ≫ I.moduleCompletionπ H n
  rw [moduleCompletionHom_π, Category.assoc, moduleCompletionHom_π, moduleCompletionHom_π_assoc,
    moduleCompletionObjHom_comp]

/-- **The completion functor** `F ↦ F̂ = lim_n (F / I ^ (n + 1) F)|_Y` from `𝒪_X`-modules to
modules over the structure sheaf of the formal completion. -/
def moduleCompletionFunctor : X.Modules ⥤ SheafOfModules.{u} I.formalCompletionRingCatSheaf where
  obj F := I.moduleCompletion F
  map φ := I.moduleCompletionHom φ
  map_id _ := I.moduleCompletionHom_id
  map_comp φ ψ := I.moduleCompletionHom_comp φ ψ

end Functoriality

end QuasicoherentIdealSubsheaf

end Hartshorne
