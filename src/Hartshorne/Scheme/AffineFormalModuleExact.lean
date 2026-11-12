/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ModuleCohomologyComparison
import Hartshorne.Scheme.FormalCompletionModuleAffineSections
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.RingTheory.AdicCompletion.Exactness

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
* The sections of the levels `(F / I ^ (n + 1) F)|_Y` over affine opens are computed in
  `Hartshorne.Scheme.FormalCompletionModuleAffineSections`.
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

section AdicLift

open Submodule AdicCompletion

/-- Over a Noetherian ring, adic completion preserves exactness of `N' → N → N''` at `N` for
`N` and `N''` finite (no surjectivity or injectivity of the maps is assumed). -/
theorem adicCompletion_map_exact {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)
    {N' N N'' : Type u} [AddCommGroup N'] [Module R N'] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [AddCommGroup N''] [Module R N''] [Module.Finite R N'']
    {u : N' →ₗ[R] N} {v : N →ₗ[R] N''} (huv : Function.Exact u v) :
    Function.Exact (AdicCompletion.map J u) (AdicCompletion.map J v) := by
  have hker : ∀ x, x ∈ LinearMap.range u ↔ x ∈ LinearMap.ker v := fun x =>
    ⟨fun ⟨y, hy⟩ => (huv x).2 ⟨y, hy⟩, fun hx => (huv x).1 hx⟩
  let u₀ : N' →ₗ[R] LinearMap.ker v :=
    u.codRestrict (LinearMap.ker v) (fun y => (hker (u y)).1 ⟨y, rfl⟩)
  have hu₀ : Function.Surjective u₀ := fun ⟨x, hx⟩ => by
    obtain ⟨y, hy⟩ := (hker x).2 hx
    exact ⟨y, Subtype.ext hy⟩
  have hex : Function.Exact (LinearMap.ker v).subtype v.rangeRestrict := fun x => by
    rw [← ZeroMemClass.coe_eq_zero]
    exact v.exact_subtype_ker_map x
  have hmex := AdicCompletion.map_exact (I := J) (Submodule.injective_subtype _) hex
    (LinearMap.surjective_rangeRestrict v)
  have hinj := AdicCompletion.map_injective J (Submodule.injective_subtype (LinearMap.range v))
  have hsurj := AdicCompletion.map_surjective J hu₀
  have hu : u = (LinearMap.ker v).subtype ∘ₗ u₀ := rfl
  have hv : v = (LinearMap.range v).subtype ∘ₗ v.rangeRestrict := rfl
  intro x
  constructor
  · intro hx
    have h0 : AdicCompletion.map J v.rangeRestrict x = 0 := by
      apply hinj
      rw [AdicCompletion.map_comp_apply, ← hv, hx, _root_.map_zero]
    obtain ⟨z, rfl⟩ := (hmex x).1 h0
    obtain ⟨w, rfl⟩ := hsurj z
    exact ⟨w, by rw [AdicCompletion.map_comp_apply, ← hu]⟩
  · rintro ⟨w, rfl⟩
    rw [AdicCompletion.map_comp_apply]
    have : v ∘ₗ u = 0 := LinearMap.ext fun y => (huv (u y)).2 ⟨y, rfl⟩
    rw [this, AdicCompletion.map_zero, LinearMap.zero_apply]

/-- **Lifting compatible sequences along an exact sequence.** Over a Noetherian ring, for
`N' → N → N''` exact at `N` with `N`, `N''` finite, a sequence `s` in `N` that is Cauchy with
`s (n + 1) ≡ s n` modulo `J ^ (n + 1)` and maps into `J ^ (n + 1) N''` at level `n` lifts, up to
`J ^ (n + 1) N`, to a sequence in `N'` with the same Cauchy property. -/
theorem exists_lift_of_exact {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)
    {N' N N'' : Type u} [AddCommGroup N'] [Module R N'] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [AddCommGroup N''] [Module R N''] [Module.Finite R N'']
    {u : N' →ₗ[R] N} {v : N →ₗ[R] N''} (huv : Function.Exact u v) (s : ℕ → N)
    (hs : ∀ n, s (n + 1) - s n ∈ J ^ (n + 1) • (⊤ : Submodule R N))
    (hv : ∀ n, v (s n) ∈ J ^ (n + 1) • (⊤ : Submodule R N'')) :
    ∃ t : ℕ → N', (∀ n, t (n + 1) - t n ∈ J ^ (n + 1) • (⊤ : Submodule R N')) ∧
      ∀ n, u (t n) - s n ∈ J ^ (n + 1) • (⊤ : Submodule R N) := by
  have hle : ∀ n, J ^ (n + 1) • (⊤ : Submodule R N) ≤ J ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))
  let x : AdicCauchySequence J N := AdicCauchySequence.mk J N s (fun n => by
    rw [SModEq.sub_mem, ← Submodule.neg_mem_iff, neg_sub]
    exact hle n (hs n))
  have hx0 : AdicCompletion.map J v (AdicCompletion.mk J N x) = 0 := by
    ext n
    rw [AdicCompletion.map_mk]
    simp only [AdicCompletion.mk_apply_coe, AdicCompletion.val_zero, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) (hv n))
  obtain ⟨w, hw⟩ := ((adicCompletion_map_exact J huv) _).1 hx0
  choose t ht using fun n => Submodule.Quotient.mk_surjective _ (w.val (n + 1))
  refine ⟨t, fun n => ?_, fun n => ?_⟩
  · have h1 := w.property (Nat.le_succ (n + 1))
    rw [← ht, ← ht] at h1
    simp only [AdicCompletion.transitionMap] at h1
    rw [← Submodule.neg_mem_iff, neg_sub]
    exact (Submodule.Quotient.eq _).1 h1.symm
  · have h1 := congrArg (fun y => y.val (n + 1)) hw
    simp only [AdicCompletion.map_val_apply, AdicCompletion.mk_apply_coe, Submodule.mkQ_apply] at h1
    rw [← ht] at h1
    simp only [LinearMap.reduceModIdeal_apply] at h1
    have h2 : u (t n) - s (n + 1) ∈ J ^ (n + 1) • (⊤ : Submodule R N) :=
      (Submodule.Quotient.eq _).1 h1
    have := Submodule.add_mem _ h2 (hs n)
    rwa [sub_add_sub_cancel] at this

end AdicLift

section SequenceLimitSections

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {C' : Type*} [Category C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{u}}
  {G : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R'}
  {D : ℕᵒᵖ ⥤ SheafOfModules.{u} R} {c : Cone D} (hc : IsLimit (G.mapCone c))

include hc in
/-- Sections of the image under `G` of a limit of an inverse sequence of sheaves of modules,
when `G` preserves it: a family of sections of the `G (D n)`, compatible with the transition
maps, comes from a section of the limit. The family is given as the images of sections `t n` of
a fixed sheaf under maps `θ n`. -/
lemma exists_sections_isLimit_mapCone (f : ∀ n, G.obj (D.obj (op (n + 1))) ⟶ G.obj (D.obj (op n)))
    (hf : ∀ n, G.map (D.map (homOfLE (Nat.le_succ n)).op) = f n) {M : SheafOfModules.{u} R'}
    (θ : ∀ n, M ⟶ G.obj (D.obj (op n))) (hθ : ∀ n, θ (n + 1) ≫ f n = θ n) (V : C'ᵒᵖ)
    (t : ℕ → M.val.obj V) (ht : ∀ n, (θ n).val.app V (t (n + 1)) = (θ n).val.app V (t n)) :
    ∃ z : (G.obj c.pt).val.obj V,
      ∀ n, (G.map (c.π.app (op n))).val.app V z = (θ n).val.app V (t n) := by
  let E := SheafOfModules.evaluation R' V ⋙ forget _
  have hc' : IsLimit (E.mapCone (G.mapCone c)) := isLimitOfPreserves E hc
  let π : (Functor.const ℕᵒᵖ).obj PUnit.{u + 1} ⟶ (D ⋙ G) ⋙ E :=
    NatTrans.ofOpSequence (fun n => TypeCat.ofHom (fun _ => (θ n).val.app V (t n))) (fun n => by
      ext ⟨⟩
      have : (f n).val.app V ((θ (n + 1)).val.app V (t (n + 1))) = (θ n).val.app V (t n) := by
        rw [← ht n, ← hθ n]
        rfl
      rw [← hf n] at this
      exact this.symm)
  refine ⟨hc'.lift ⟨PUnit, π⟩ PUnit.unit, fun n => ?_⟩
  exact ConcreteCategory.congr_hom (hc'.fac ⟨PUnit, π⟩ (op n)) PUnit.unit

include hc in
/-- Sections of the image under `G` of a preserved limit of an inverse sequence are determined
by their projections. -/
lemma sections_isLimit_mapCone_ext (V : C'ᵒᵖ) (z z' : (G.obj c.pt).val.obj V)
    (h : ∀ n, (G.map (c.π.app (op n))).val.app V z = (G.map (c.π.app (op n))).val.app V z') :
    z = z' := by
  let E := SheafOfModules.evaluation R' V ⋙ forget _
  have hc' : IsLimit (E.mapCone (G.mapCone c)) := isLimitOfPreserves E hc
  have := hc'.hom_ext (W := PUnit.{u + 1}) (f := TypeCat.ofHom fun _ => z)
    (f' := TypeCat.ofHom fun _ => z') (fun ⟨n⟩ => by ext ⟨⟩; exact h n)
  exact ConcreteCategory.congr_hom this PUnit.unit

end SequenceLimitSections

section CompSections

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Sections of a composite, for a commutative square `f ≫ g = f' ≫ g'`. -/
lemma sheafOfModules_val_app_apply_of_comp_eq_comp {M N N' P : SheafOfModules.{u} R}
    {f : M ⟶ N} {g : N ⟶ P} {f' : M ⟶ N'} {g' : N' ⟶ P} (e : f ≫ g = f' ≫ g') (V : Cᵒᵖ)
    (x : M.val.obj V) : g.val.app V (f.val.app V x) = g'.val.app V (f'.val.app V x) := by
  have := congrArg (fun φ => φ.val.app V x) e
  exact this

end CompSections

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

section AffineExactness

open Scheme.Modules

variable (χ : X.ringCatSheaf ⟶
    ((Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj I.formalCompletionRingCatSheaf)
  (hχ : ∀ (n : ℕ) (V : X.Opensᵒᵖ) (r : X.ringCatSheaf.obj.obj V),
    (I.infinitesimalNeighborhood (n + 1)).ringCatSheaf.obj.map
        ((I.functorToPreimageInfinitesimalNeighborhoodι n).app V.unop).op
        ((I.infinitesimalNeighborhoodι (n + 1)).toRingCatSheafHom.hom.app V r) =
      (I.formalCompletionRingCatSheafπ n).hom.app
        (op ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj V.unop)) (χ.hom.app V r))

/-- **Naturality of the canonical maps** `F ⟶ i_* (F / I ^ (n + 1) F)|_Y` in `F`. -/
lemma moduleCompletionLevelMap_naturality {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    I.moduleCompletionLevelMap χ hχ F n ≫
        (SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionObjHom φ n) =
      φ ≫ I.moduleCompletionLevelMap χ hχ G n := by
  have h1 := sheafOfModulesPushforwardRestrictToComp_naturality
    (I.functorToPreimageInfinitesimalNeighborhoodι n) (I.formalCompletionRingCatSheafπ n) χ
    (I.infinitesimalNeighborhoodι (n + 1)).toRingCatSheafHom (hχ n)
    ((Scheme.Modules.pullback (I.infinitesimalNeighborhoodι (n + 1))).map
      (I.moduleCompletionQuotientHom φ n))
  have h2 := (pullbackPushforwardAdjunction (I.infinitesimalNeighborhoodι (n + 1))).unit_naturality
    (I.moduleCompletionQuotientHom φ n)
  have h3 := I.π_moduleCompletionQuotientHom φ n
  unfold moduleCompletionLevelMap moduleCompletionObjHom
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ ((Category.assoc _ _ _).trans
    ((whisker_eq _ h1.symm).trans ((Category.assoc _ _ _).symm.trans
      ((eq_whisker h2 _).trans (Category.assoc _ _ _)))))).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker h3 _).trans (Category.assoc _ _ _))

/-- The canonical maps are natural, on sections over `U`. -/
lemma moduleCompletionObjHom_val_app_moduleCompletionLevelMap {G G' : X.Modules} (φ : G ⟶ G')
    (n : ℕ) (U : X.Opens) (t : Γ(G, U)) :
    ((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionObjHom φ n)).val.app
        (op U) ((I.moduleCompletionLevelMap χ hχ G n).val.app (op U) t) =
      (I.moduleCompletionLevelMap χ hχ G' n).val.app (op U) (φ.app U t) :=
  sheafOfModules_val_app_apply_of_comp_eq_comp (I.moduleCompletionLevelMap_naturality χ hχ φ n) _ t

/-- The completion of a morphism, on sections of the pushforwards to `X`. -/
lemma moduleCompletionπ_val_app_moduleCompletionHom {G G' : X.Modules} (φ : G ⟶ G') (n : ℕ)
    (U : X.Opens)
    (w : ((SheafOfModules.pushforward.{u} χ).obj (I.moduleCompletion G)).val.obj (op U)) :
    ((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionπ G' n)).val.app
        (op U) (((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionHom φ)).val.app
          (op U) w) =
      ((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionObjHom φ n)).val.app
        (op U) (((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionπ G n)).val.app
          (op U) w) :=
  sheafOfModules_val_app_apply_of_comp_eq_comp
    (((SheafOfModules.pushforward.{u} χ).map_comp _ _).symm.trans
      ((congrArg _ (I.moduleCompletionHom_π φ n)).trans
        ((SheafOfModules.pushforward.{u} χ).map_comp _ _))) _ w

/-- The projections of the completion, on sections of the pushforwards to `X`. -/
lemma moduleCompletionMap_val_app_moduleCompletionπ (G : X.Modules) (n : ℕ) (U : X.Opens)
    (w : ((SheafOfModules.pushforward.{u} χ).obj (I.moduleCompletion G)).val.obj (op U)) :
    ((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionMap G n)).val.app
        (op U) (((SheafOfModules.pushforward.{u} χ).map
          (I.moduleCompletionπ G (n + 1))).val.app (op U) w) =
      ((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionπ G n)).val.app (op U) w :=
  sheafOfModules_val_app_apply_of_comp_eq
    (((SheafOfModules.pushforward.{u} χ).map_comp _ _).symm.trans
      (congrArg _ (I.moduleCompletionπ_comp_moduleCompletionMap G n))) _ w

include hχ in
/-- A sequence of sections `t n` of `G` over `U` that is Cauchy for `I(U)` defines a section of
the completion `Ĝ` over `U ∩ |Y|` (of its pushforward to `X`), whose components are the images
of the `t n`. -/
lemma exists_moduleCompletion_sections (G : X.Modules) [G.IsQuasicoherent] (U : X.affineOpens)
    (t : ℕ → Γ(G, (U : X.Opens)))
    (ht : ∀ n, t (n + 1) - t n ∈
      I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(G, (U : X.Opens)))) :
    ∃ z : ((SheafOfModules.pushforward.{u} χ).obj (I.moduleCompletion G)).val.obj
        (op (U : X.Opens)),
      ∀ n, ((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionπ G n)).val.app
        (op (U : X.Opens)) z =
        (I.moduleCompletionLevelMap χ hχ G n).val.app (op (U : X.Opens)) (t n) := by
  have : (PresheafOfModules.pushforward.{u} χ.hom).IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top _)
  have : (SheafOfModules.pushforward.{u} χ).IsRightAdjoint :=
    (SheafOfModules.PullbackConstruction.adjunction.{u} _).isRightAdjoint
  have hc := isLimitOfPreserves (SheafOfModules.pushforward.{u} χ)
    (limit.isLimit (I.moduleCompletionDiagram G))
  refine exists_sections_isLimit_mapCone hc
    (fun n => (SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionMap G n))
    (fun n => congrArg _ (Functor.ofOpSequence_map_homOfLE_succ _ n))
    (fun n => I.moduleCompletionLevelMap χ hχ G n)
    (fun n => I.moduleCompletionLevelMap_comp_moduleCompletionMap χ hχ G n) (op (U : X.Opens)) t
    (fun n => sub_eq_zero.1 ((map_sub _ _ _).symm.trans
      ((I.moduleCompletionSectionsMap_eq_zero_iff G n U _).2 (ht n))))

include hχ in
/-- **Exactness of the completion over an affine open**, on sections of the pushforwards to `X`.
Let `F' ⟶ F ⟶ F''` be quasi-coherent modules whose sections over the affine open `U` form an exact
sequence of finite modules over the Noetherian ring `Γ(U, 𝒪_X)`. Then a section of `F̂` over
`U ∩ |Y|` killed by `F̂ ⟶ F̂''` comes from `F̂'`. -/
theorem moduleCompletionHom_exists_preimage {F' F F'' : X.Modules} [F'.IsQuasicoherent]
    [F.IsQuasicoherent] [F''.IsQuasicoherent] (u : F' ⟶ F) (v : F ⟶ F'') (U : X.affineOpens)
    [IsNoetherianRing Γ(X, (U : X.Opens))] [Module.Finite Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens))]
    [Module.Finite Γ(X, (U : X.Opens)) Γ(F'', (U : X.Opens))]
    (hexact : Function.Exact (u.app U) (v.app U))
    (x : ((SheafOfModules.pushforward.{u} χ).obj (I.moduleCompletion F)).val.obj
      (op (U : X.Opens)))
    (hx : ((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionHom v)).val.app
      (op (U : X.Opens)) x = 0) :
    ∃ y, ((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionHom u)).val.app
      (op (U : X.Opens)) y = x := by
  have hxs := fun n => I.moduleCompletionMap_val_app_moduleCompletionπ χ F n U x
  choose s hs using fun n => I.moduleCompletionSectionsMap_surjective F n U
    (((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionπ F n)).val.app
      (op (U : X.Opens)) x)
  have hker : ∀ (G : X.Modules) [G.IsQuasicoherent] (n : ℕ) (t : Γ(G, (U : X.Opens))),
      (I.moduleCompletionLevelMap χ hχ G n).val.app (op (U : X.Opens)) t = 0 ↔
        t ∈ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(G, (U : X.Opens))) :=
    fun G _ n t => I.moduleCompletionSectionsMap_eq_zero_iff G n U t
  have hs' : ∀ n, (I.moduleCompletionLevelMap χ hχ F n).val.app (op (U : X.Opens)) (s n) =
      ((SheafOfModules.pushforward.{u} χ).map (I.moduleCompletionπ F n)).val.app
        (op (U : X.Opens)) x := fun n =>
    (I.moduleCompletionLevelMap_val_app χ hχ F n U (s n)).trans (hs n)
  -- the lifts `s n` form a Cauchy sequence
  have hS : ∀ n, s (n + 1) - s n ∈
      I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens))) := by
    intro n
    have a1 := (I.moduleCompletionMap_val_app_moduleCompletionLevelMap χ hχ F n U (s (n + 1))).symm.trans
      ((congrArg (fun y => ((SheafOfModules.pushforward.{u} χ).map
        (I.moduleCompletionMap F n)).val.app (op (U : X.Opens)) y) (hs' (n + 1))).trans (hxs n))
    exact (hker F n _).1 ((map_sub _ _ _).trans (sub_eq_zero.2 (a1.trans (hs' n).symm)))
  have hnat := fun {G G' : X.Modules} (φ : G ⟶ G') n t =>
    I.moduleCompletionObjHom_val_app_moduleCompletionLevelMap χ hχ φ n U t
  have hπ := fun {G G' : X.Modules} (φ : G ⟶ G') n w =>
    I.moduleCompletionπ_val_app_moduleCompletionHom χ φ n U w
  -- `v (s n) ∈ I(U) ^ (n + 1) Γ(U, F'')`
  have hV : ∀ n, v.app U (s n) ∈
      I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F'', (U : X.Opens))) := by
    intro n
    refine (hker F'' n _).1 ?_
    refine (hnat v n (s n)).symm.trans ?_
    refine (congrArg (fun y => ((SheafOfModules.pushforward.{u} χ).map
      (I.moduleCompletionObjHom v n)).val.app (op (U : X.Opens)) y) (hs' n)).trans ?_
    refine (hπ v n x).symm.trans ?_
    refine (congrArg (fun y => ((SheafOfModules.pushforward.{u} χ).map
      (I.moduleCompletionπ F'' n)).val.app (op (U : X.Opens)) y) hx).trans ?_
    exact map_zero _
  -- lift along the exact sequence of sections
  let uL : Γ(F', (U : X.Opens)) →ₗ[Γ(X, (U : X.Opens))] Γ(F, (U : X.Opens)) :=
    { toFun := u.app U, map_add' := map_add _, map_smul' := Hom.app_smul u }
  let vL : Γ(F, (U : X.Opens)) →ₗ[Γ(X, (U : X.Opens))] Γ(F'', (U : X.Opens)) :=
    { toFun := v.app U, map_add' := map_add _, map_smul' := Hom.app_smul v }
  obtain ⟨t, ht1, ht2⟩ := exists_lift_of_exact (u := uL) (v := vL) (I.ideal U) hexact s hS hV
  obtain ⟨z, hz⟩ := I.exists_moduleCompletion_sections χ hχ F' U t ht1
  have : (PresheafOfModules.pushforward.{u} χ.hom).IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top _)
  have : (SheafOfModules.pushforward.{u} χ).IsRightAdjoint :=
    (SheafOfModules.PullbackConstruction.adjunction.{u} _).isRightAdjoint
  have hc₀ := isLimitOfPreserves (SheafOfModules.pushforward.{u} χ)
    (limit.isLimit (I.moduleCompletionDiagram F))
  refine ⟨z, sections_isLimit_mapCone_ext hc₀ (op (U : X.Opens)) _ _ (fun n => ?_)⟩
  refine (hπ u n z).trans ?_
  refine (congrArg (fun y => ((SheafOfModules.pushforward.{u} χ).map
    (I.moduleCompletionObjHom u n)).val.app (op (U : X.Opens)) y) (hz n)).trans ?_
  refine (hnat u n (t n)).trans ?_
  refine Eq.trans ?_ (hs' n)
  exact sub_eq_zero.1 ((map_sub _ _ _).symm.trans ((hker F n _).2 (ht2 n)))

end AffineExactness

end QuasicoherentIdealSubsheaf

end Hartshorne
