/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModuleReconstruction

/-!
# Completeness of a module for an ideal subsheaf is local

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.6(a) (pp. 197–198): the locality step.

Let `X` be a locally ringed space, `J` an ideal subsheaf of `𝒪_X` and `F` an `𝒪_X`-module. Say
`F` is complete for `J` when `F ⟶ lim_n F / J ^ (n + 1) F`
(`Hartshorne.IdealSubsheaf.toLimitPowQuotient`) is an isomorphism.

* `Hartshorne.sheafOfModules_isIso_of_bijective`: a morphism of sheaves of modules bijective on
  sections over the opens of a basis is an isomorphism.
* `Hartshorne.IdealSubsheaf.isIso_toLimitPowQuotient_of_isLimit`: `F` is complete for `J` as soon
  as, over every open `W` of a basis, `F(W)` is the limit of the `(F / J ^ (n + 1) F)(W)`;
  `IdealSubsheaf.isLimitPowQuotientConeSections` is the converse.
* `Hartshorne.IdealSubsheaf.restrict`: the restriction `J|_U` to an open subspace, with
  `IdealSubsheaf.restrict_pow` (`J|_U ^ k = (J ^ k)|_U`) and
  `IdealSubsheaf.mem_restrict_smulSubmodule_iff` (restriction commutes with `J F`).
* `Hartshorne.IdealSubsheaf.restrictPowQuotientIso`: `F|_U / J|_U ^ (n + 1) F|_U` is the
  restriction of `F / J ^ (n + 1) F`; `IdealSubsheaf.nonempty_isLimit_restrict_iff` is the
  corresponding statement on sections.
* `Hartshorne.IdealSubsheaf.isIso_toLimitPowQuotient_of_iSup_eq_top`: if `X = ⋃ Uᵢ` and each
  `F|_{Uᵢ}` is complete for `J|_{Uᵢ}`, then `F` is complete for `J`.
* `Hartshorne.IdealSubsheaf.mem_powSubmodule_of_powQuotientπ_app_eq_zero`: the kernel of
  `F(W) ⟶ (F / J ^ (n + 1) F)(W)` is `(J ^ (n + 1) F)(W)`.
* `Hartshorne.IdealSubsheaf.isIso_toLimitPowQuotient_iff_of_kernel`: if epimorphisms
  `π n : F ⟶ Q n` with kernels `J ^ (n + 1) F` are compatible with maps `Q (n + 1) ⟶ Q n`, then
  `F` is complete for `J` iff `F` is the limit of the `Q n` (`IdealSubsheaf.coneOfπ`); the
  quotients are identified by `IdealSubsheaf.powQuotientIsoOfKernel`.
* `Hartshorne.IdealSubsheaf.isIso_toLimitPowQuotient_of_iso`: completeness is invariant under
  isomorphism of modules; `IdealSubsheaf.map_mem_smulSubmodule`: a morphism maps `J M` into
  `J N`.

The restricted quotient is identified through exactness, checked on sections, rather than through
a general statement that restriction to an open preserves cokernels.
-/

noncomputable section
open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne
universe u

/-- A morphism of sheaves of modules which is bijective on sections over every open of a basis is
an isomorphism. -/
theorem sheafOfModules_isIso_of_bijective {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} {M N : SheafOfModules.{u} R}
    (φ : M ⟶ N) {ι : Type u} (B : ι → Opens T) (hB : Opens.IsBasis (Set.range B))
    (h : ∀ i, Function.Bijective (φ.val.app (op (B i)))) : IsIso φ := by
  have : IsIso ((SheafOfModules.toSheaf R).map φ) :=
    TopCat.Sheaf.isIso_iff_isIso_basis hB fun i =>
      (ConcreteCategory.isIso_iff_bijective _).mpr (h i)
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf R)

namespace IdealSubsheaf
variable {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T} (J : IdealSubsheaf R)
  (M : SheafOfModules.{u} (ringCatSheafOf R))

/-- Sections over `W` of the cone `M ⟶ M / J ^ (n + 1) M`, as a cone of types. -/
abbrev powQuotientConeSections (W : Opens T) :=
  (SheafOfModules.evaluation (ringCatSheafOf R) (op W) ⋙ forget _).mapCone (J.powQuotientCone M)

/-- If `M ⟶ lim_n M / J ^ (n + 1) M` is an isomorphism, the cone of projections is a limit. -/
def isLimitPowQuotientConeOfIsIso [IsIso (J.toLimitPowQuotient M)] :
    IsLimit (J.powQuotientCone M) :=
  haveI : IsIso ((limit.isLimit (J.powQuotientDiagram M)).lift (J.powQuotientCone M)) :=
    ‹IsIso (J.toLimitPowQuotient M)›
  IsLimit.ofPointIso (limit.isLimit _)

private def isLimitSections {c : Cone (J.powQuotientDiagram M)} (hc : IsLimit c) (W : Opens T) :
    IsLimit ((SheafOfModules.evaluation (ringCatSheafOf R) (op W) ⋙ forget _).mapCone c) :=
  haveI := SheafOfModules.evaluationPreservesLimit (J.powQuotientDiagram M) (op W)
  isLimitOfPreserves (forget _) (isLimitOfPreserves (SheafOfModules.evaluation _ (op W)) hc)

/-- If `M ⟶ lim_n M / J ^ (n + 1) M` is an isomorphism, then on sections over every open `W`,
`M(W)` is the limit of the sections of the `M / J ^ (n + 1) M`. -/
def isLimitPowQuotientConeSections [IsIso (J.toLimitPowQuotient M)] (W : Opens T) :
    IsLimit (J.powQuotientConeSections M W) :=
  isLimitSections J M (J.isLimitPowQuotientConeOfIsIso M) W

/-- Conversely, if on sections over every open of a basis `M(W)` is the limit of the sections of
the `M / J ^ (n + 1) M`, then `M ⟶ lim_n M / J ^ (n + 1) M` is an isomorphism. -/
theorem isIso_toLimitPowQuotient_of_isLimit {ι : Type u} (B : ι → Opens T)
    (hB : Opens.IsBasis (Set.range B))
    (h : ∀ i, Nonempty (IsLimit (J.powQuotientConeSections M (B i)))) :
    IsIso (J.toLimitPowQuotient M) := by
  refine sheafOfModules_isIso_of_bijective _ B hB fun i => ?_
  obtain ⟨hc⟩ := h i
  let E := SheafOfModules.evaluation (ringCatSheafOf R) (op (B i)) ⋙ forget _
  have hl := isLimitSections J M (limit.isLimit (J.powQuotientDiagram M)) (B i)
  have he : E.map (J.toLimitPowQuotient M) = (hc.conePointUniqueUpToIso hl).hom :=
    hl.hom_ext fun j => Eq.trans ((E.map_comp _ _).symm.trans
      (congrArg E.map (limit.lift_π _ _))) (IsLimit.conePointUniqueUpToIso_hom_comp hc hl j).symm
  have : IsIso (E.map (J.toLimitPowQuotient M)) := by
    rw [he]; exact (hc.conePointUniqueUpToIso hl).isIso_hom
  exact (CategoryTheory.isIso_iff_bijective _).mp this


/-- A section of `M` whose image in `M / J ^ (n + 1) M` vanishes lies in `J ^ (n + 1) M`. -/
lemma mem_powSubmodule_of_powQuotientπ_app_eq_zero (n : ℕ) {W : Opens T}
    (s : M.val.obj (op W)) (hs : (J.powQuotientπ M n).val.app (op W) s = 0) :
    s ∈ (J.powSubmodule M n).obj (op W) := by
  let S := ShortComplex.mk _ _ (cokernel.condition ((J ^ (n + 1)).smulι M))
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel _)
  have : Mono S.f :=
    haveI := (SheafOfModules.fullyFaithfulForget (ringCatSheafOf R)).faithful
    (SheafOfModules.forget (ringCatSheafOf R)).mono_of_mono_map
      (inferInstanceAs (Mono ((J ^ (n + 1)).smulSubmodule M).ι))
  let G := SheafOfModules.evaluation (ringCatSheafOf R) (op W)
  have hG : PreservesFiniteLimits G :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits (ringCatSheafOf R) (op W)
  have : G.Additive := ⟨fun {_ _ _ _} => rfl⟩
  have key : PreservesFiniteLimits G → ∀ S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R)),
      S.Exact ∧ Mono S.f → (S.map G).Exact ∧ Mono (G.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae G).out 3 1).mp
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).mp (key hG S ⟨hS, inferInstance⟩).1 s hs
  rw [← ht]
  exact t.2

/-- The image in `M / J ^ (n + 1) M` of a section of `J ^ (n + 1) M` vanishes. -/
lemma powQuotientπ_app_eq_zero (n : ℕ) {W : Opens T} (s : M.val.obj (op W))
    (hs : s ∈ (J.powSubmodule M n).obj (op W)) : (J.powQuotientπ M n).val.app (op W) s = 0 :=
  congrArg (fun k => k.val.app (op W) ⟨s, hs⟩) (cokernel.condition ((J ^ (n + 1)).smulι M))

end IdealSubsheaf

namespace IdealSubsheaf

variable {X : LocallyRingedSpace.{u}} {U : TopCat.{u}} {f : U ⟶ X.toTopCat}
  (h : Topology.IsOpenEmbedding f) (J : IdealSubsheaf X.sheaf)

/-- **The restriction `J|_U`** of an ideal subsheaf of `𝒪_X` to an open subspace `U`: its ideal
over `V ⊆ U` is the ideal of `J` over the image of `V`. -/
def restrict : IdealSubsheaf (X.restrict h).sheaf :=
  ofIdeals _ (fun V => J.ideal (h.functor.obj V))
    (fun hWV => J.ideal_le_comap (h.functor.monotone hWV))
    (fun {V} s hs => J.mem_ideal_of_locally s fun y hy => by
      obtain ⟨x, hxV, rfl⟩ := hy
      obtain ⟨W, hWV, hxW, hsW⟩ := hs x hxV
      exact ⟨h.functor.obj W, h.functor.monotone hWV, ⟨x, hxW, rfl⟩, hsW⟩)

lemma restrict_ideal (V : Opens U) : (J.restrict h).ideal V = J.ideal (h.functor.obj V) := rfl

omit J in
/-- A local condition on sections over the opens of `U` is the same local condition on sections over
the opens of `X` contained in the image of `U`. -/
private lemma locally_iff_restrict {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    (S : (Opens X.toTopCat)ᵒᵖ ⥤ C) (P : ∀ W : Opens X.toTopCat, ToType (S.obj (op W)) → Prop)
    (hP : ∀ {W W' : Opens X.toTopCat} (hW : W' ≤ W) (t : ToType (S.obj (op W))), P W t →
      P W' (S.map (homOfLE hW).op t))
    (V : Opens U) (s : ToType (S.obj (op (h.functor.obj V)))) :
    (∀ x ∈ V, ∃ (W : Opens U) (hWV : W ≤ V), x ∈ W ∧
      P (h.functor.obj W) (S.map (homOfLE (h.functor.monotone hWV)).op s)) ↔
    (∀ y ∈ h.functor.obj V, ∃ (W : Opens X.toTopCat) (hWV : W ≤ h.functor.obj V), y ∈ W ∧
      P W (S.map (homOfLE hWV).op s)) := by
  constructor
  · rintro hs y ⟨x, hxV, rfl⟩
    obtain ⟨W, hWV, hxW, hsW⟩ := hs x hxV
    exact ⟨_, h.functor.monotone hWV, ⟨x, hxW, rfl⟩, hsW⟩
  · intro hs x hxV
    obtain ⟨W', hW'V, hxW', hsW'⟩ := hs (f x) ⟨x, hxV, rfl⟩
    refine ⟨(Opens.map f).obj W' ⊓ V, inf_le_right, ⟨hxW', hxV⟩, ?_⟩
    have hle : h.functor.obj ((Opens.map f).obj W' ⊓ V) ≤ W' := by
      rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
      exact hz
    have := hP hle _ hsW'
    rwa [← ConcreteCategory.comp_apply, ← S.map_comp] at this

/-- Restriction of sections maps `J(W) ^ k` into `J(W') ^ k`. -/
private lemma map_mem_ideal_pow {W W' : Opens X.toTopCat} (hW : W' ≤ W) (k : ℕ)
    {t : X.presheaf.obj (op W)} (ht : t ∈ J.ideal W ^ k) :
    X.presheaf.map (homOfLE hW).op t ∈ J.ideal W' ^ k := by
  have h1 : Ideal.map (X.presheaf.map (homOfLE hW).op).hom (J.ideal W) ≤ J.ideal W' :=
    Ideal.map_le_iff_le_comap.mpr (J.ideal_le_comap hW)
  exact Ideal.pow_right_mono h1 k
    ((Ideal.map_pow (X.presheaf.map (homOfLE hW).op).hom (I := J.ideal W) k).le
      (Ideal.mem_map_of_mem _ ht))

/-- Restriction commutes with powers: `J|_U ^ k = (J ^ k)|_U`. -/
lemma restrict_pow (k : ℕ) : J.restrict h ^ k = (J ^ k).restrict h := by
  ext V s
  exact locally_iff_restrict h X.presheaf (fun W t => t ∈ J.ideal W ^ k)
    (fun hW t ht => J.map_mem_ideal_pow hW k ht) V s

variable (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf))

/-- The restriction `F|_U` of an `𝒪_X`-module, as a module over the structure sheaf of `U` in the
form used for ideal subsheaves. -/
abbrev restrictModule : SheafOfModules.{u} (ringCatSheafOf (X.restrict h).sheaf) :=
  (structureModuleRestrict X h).obj F

/-- Restriction commutes with `J M`: a section of `F|_U` over `V` lies in `J|_U F|_U` iff, as a
section of `F` over the image of `V`, it lies in `J F`. -/
lemma mem_restrict_smulSubmodule_iff (V : Opens U)
    (s : (restrictModule h F).val.obj (op V)) :
    s ∈ ((J.restrict h).smulSubmodule (restrictModule h F)).obj (op V) ↔
      (show F.val.obj (op (h.functor.obj V)) from s) ∈
        (J.smulSubmodule F).obj (op (h.functor.obj V)) :=
  locally_iff_restrict h F.val.presheaf
    (fun W (t : ToType (F.val.presheaf.obj (op W))) =>
      (show F.val.obj (op W) from t) ∈ J.sectionsSmul F W)
    (fun hW _ ht => J.map_mem_sectionsSmul F hW ht) V s

variable (n : ℕ)

/-- The projection `F|_U ⟶ (F / J ^ (n + 1) F)|_U`. -/
abbrev restrictPowQuotientπ :
    restrictModule h F ⟶ restrictModule h (J.powQuotient F n) :=
  (structureModuleRestrict X h).map (J.powQuotientπ F n)

lemma smulι_restrictPowQuotientπ :
    ((J.restrict h) ^ (n + 1)).smulι (restrictModule h F) ≫ restrictPowQuotientπ h J F n = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  ext ⟨s, hs⟩
  rw [restrict_pow] at hs
  exact J.powQuotientπ_app_eq_zero F n _ ((mem_restrict_smulSubmodule_iff h _ F V.unop s).mp hs)

/-- The short complex `J|_U ^ (n + 1) F|_U ⟶ F|_U ⟶ (F / J ^ (n + 1) F)|_U`. -/
abbrev restrictPowShortComplex :
    ShortComplex (SheafOfModules.{u} (ringCatSheafOf (X.restrict h).sheaf)) :=
  ShortComplex.mk _ _ (smulι_restrictPowQuotientπ h J F n)

lemma restrictPowShortComplex_exact : (restrictPowShortComplex h J F n).Exact := by
  refine sheafOfModules_exact_of_isBasis_sections _ (B := Set.univ)
    (Opens.isBasis_iff_nbhd.mpr fun {V x} hx => ⟨V, trivial, hx, le_rfl⟩) ?_
  intro V _ x hx
  have hmem := J.mem_powSubmodule_of_powQuotientπ_app_eq_zero F n _ hx
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [restrict_pow]
  exact (mem_restrict_smulSubmodule_iff h _ F V x).mpr hmem

instance epi_restrictPowQuotientπ : Epi (restrictPowQuotientπ h J F n) := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf _).map (restrictPowQuotientπ h J F n)).hom := by
    refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun V t x hx => ?_
    obtain ⟨W', hW'V, hxW', s, hs⟩ :=
      sheafOfModules_exists_local_lift (J.powQuotientπ F n) t (x := f x) ⟨x, hx, rfl⟩
    have hle : h.functor.obj ((Opens.map f).obj W' ⊓ V) ≤ W' := by
      rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
      exact hz
    refine ⟨(Opens.map f).obj W' ⊓ V, inf_le_right,
      ⟨F.val.presheaf.map (homOfLE hle).op s, ?_⟩, ⟨hxW', hx⟩⟩
    have e1 := PresheafOfModules.naturality_apply (J.powQuotientπ F n).val (homOfLE hle).op s
    rw [hs] at e1
    refine e1.trans ?_
    exact ((J.powQuotient F n).val.map_comp_apply (homOfLE hW'V).op (homOfLE hle).op t).symm
  have : Epi ((SheafOfModules.toSheaf _).map (restrictPowQuotientπ h J F n)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hls
  exact (SheafOfModules.toSheaf _).epi_of_epi_map this

/-- **Restriction commutes with `F / J ^ (n + 1) F`**: `F|_U / J|_U ^ (n + 1) F|_U` is the
restriction of `F / J ^ (n + 1) F`. -/
def restrictPowQuotientIso :
    (J.restrict h).powQuotient (restrictModule h F) n ≅ restrictModule h (J.powQuotient F n) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (restrictPowShortComplex_exact h J F n).gIsCokernel

@[reassoc (attr := simp)]
lemma powQuotientπ_restrictPowQuotientIso_hom :
    (J.restrict h).powQuotientπ (restrictModule h F) n ≫ (restrictPowQuotientIso h J F n).hom =
      restrictPowQuotientπ h J F n :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

lemma powQuotientMap_restrictPowQuotientIso_hom :
    (J.restrict h).powQuotientMap (restrictModule h F) n ≫ (restrictPowQuotientIso h J F n).hom =
      (restrictPowQuotientIso h J F (n + 1)).hom ≫
        (show restrictModule h (J.powQuotient F (n + 1)) ⟶ restrictModule h (J.powQuotient F n) from
          (structureModuleRestrict X h).map (J.powQuotientMap F n)) := by
  refine (cancel_epi ((J.restrict h).powQuotientπ (restrictModule h F) (n + 1))).mp ?_
  rw [powQuotientπ_powQuotientMap_assoc, powQuotientπ_restrictPowQuotientIso_hom,
    powQuotientπ_restrictPowQuotientIso_hom_assoc]
  exact (((structureModuleRestrict X h).map_comp _ _).symm.trans
    (congrArg (structureModuleRestrict X h).map (J.powQuotientπ_powQuotientMap F n))).symm

variable {n}

/-- **Completeness for `J` restricts to opens, on sections**: over an open `V` of `U`, `F|_U(V)` is
the limit of the `(F|_U / J|_U ^ (n + 1) F|_U)(V)` iff `F(V)` is the limit of the
`(F / J ^ (n + 1) F)(V)`, `V` viewed as an open of `X`. -/
theorem nonempty_isLimit_restrict_iff (V : Opens U) :
    Nonempty (IsLimit ((J.restrict h).powQuotientConeSections (restrictModule h F) V)) ↔
      Nonempty (IsLimit (J.powQuotientConeSections F (h.functor.obj V))) := by
  let E := SheafOfModules.evaluation (ringCatSheafOf (X.restrict h).sheaf) (op V) ⋙ forget _
  let Ψ : (J.restrict h).powQuotientDiagram (restrictModule h F) ⋙ E ⟶
      J.powQuotientDiagram F ⋙
        (SheafOfModules.evaluation (ringCatSheafOf X.sheaf) (op (h.functor.obj V)) ⋙ forget _) :=
    NatTrans.ofOpSequence (fun n => E.map (restrictPowQuotientIso h J F n).hom) (fun n => by
      have h1 : ((J.restrict h).powQuotientDiagram (restrictModule h F)).map
          (homOfLE (n.le_add_right 1)).op = (J.restrict h).powQuotientMap (restrictModule h F) n :=
        Functor.ofOpSequence_map_homOfLE_succ _ n
      have h2 : (J.powQuotientDiagram F).map (homOfLE (n.le_add_right 1)).op =
          J.powQuotientMap F n :=
        Functor.ofOpSequence_map_homOfLE_succ _ n
      change E.map _ ≫ _ = _ ≫ E.map (show restrictModule h (J.powQuotient F (n + 1)) ⟶
          restrictModule h (J.powQuotient F n) from
          (structureModuleRestrict X h).map ((J.powQuotientDiagram F).map _))
      refine (E.map_comp _ _).symm.trans (Eq.trans (congrArg E.map ?_) (E.map_comp _ _))
      exact (congrArg (· ≫ _) h1).trans ((powQuotientMap_restrictPowQuotientIso_hom h J F n).trans
        (congrArg (_ ≫ ·) (congrArg (structureModuleRestrict X h).map h2.symm))))
  have : IsIso Ψ := by
    have : ∀ n : ℕᵒᵖ, IsIso (Ψ.app n) := fun ⟨n⟩ =>
      inferInstanceAs (IsIso (E.map (restrictPowQuotientIso h J F n).hom))
    exact NatIso.isIso_of_isIso_app _
  have e : (Cone.postcompose Ψ).obj
      ((J.restrict h).powQuotientConeSections (restrictModule h F) V) ≅
      J.powQuotientConeSections F (h.functor.obj V) :=
    Cone.ext (Iso.refl _) fun ⟨n⟩ => by
      change E.map _ ≫ E.map _ = 𝟙 _ ≫ E.map (restrictPowQuotientπ h J F n)
      exact (E.map_comp _ _).symm.trans ((congrArg E.map
        (powQuotientπ_restrictPowQuotientIso_hom h J F n)).trans (Category.id_comp _).symm)
  exact ⟨fun ⟨hc⟩ => ⟨(IsLimit.postcomposeHomEquiv (asIso Ψ) _).symm hc |>.ofIsoLimit e⟩,
    fun ⟨hc⟩ => ⟨IsLimit.postcomposeHomEquiv (asIso Ψ) _ (hc.ofIsoLimit e.symm)⟩⟩

end IdealSubsheaf

namespace IdealSubsheaf

variable {X : LocallyRingedSpace.{u}} (J : IdealSubsheaf X.sheaf)
  (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf))

private lemma functor_obj_map_obj_of_le {U W : Opens X.toTopCat} (hW : W ≤ U) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W) = W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hW hx⟩, hx, rfl⟩

/-- **Completeness for `J` is local**: if `X = ⋃ Uᵢ` and each `F|_{Uᵢ}` is complete for `J|_{Uᵢ}`,
that is `F|_{Uᵢ} ⟶ lim_n F|_{Uᵢ} / J|_{Uᵢ} ^ (n + 1) F|_{Uᵢ}` is an isomorphism, then
`F ⟶ lim_n F / J ^ (n + 1) F` is an isomorphism. -/
theorem isIso_toLimitPowQuotient_of_iSup_eq_top {ι : Type*} (U : ι → Opens X.toTopCat)
    (hU : iSup U = ⊤)
    (hF : ∀ i, IsIso ((J.restrict (U i).isOpenEmbedding).toLimitPowQuotient
      (restrictModule (U i).isOpenEmbedding F))) :
    IsIso (J.toLimitPowQuotient F) := by
  refine J.isIso_toLimitPowQuotient_of_isLimit F
    (fun W : {W : Opens X.toTopCat // ∃ i, W ≤ U i} => W.1) ?_ fun ⟨W, i, hWi⟩ => ?_
  · refine Opens.isBasis_iff_nbhd.mpr fun {W x} hx => ?_
    have hxU : x ∈ iSup U := hU ▸ trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
    exact ⟨W ⊓ U i, ⟨⟨W ⊓ U i, i, inf_le_right⟩, rfl⟩, ⟨hx, hi⟩, inf_le_left⟩
  · have := (nonempty_isLimit_restrict_iff (U i).isOpenEmbedding J F
      ((Opens.map (U i).inclusion').obj W)).mp
      ⟨(J.restrict (U i).isOpenEmbedding).isLimitPowQuotientConeSections _ _⟩
    rwa [functor_obj_map_obj_of_le hWi] at this

end IdealSubsheaf
/-! ### Completeness through a presentation of the quotients; invariance under isomorphism -/

namespace IdealSubsheaf
variable {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T} (J : IdealSubsheaf R)
  {M : SheafOfModules.{u} (ringCatSheafOf R)}
  {Q : ℕ → SheafOfModules.{u} (ringCatSheafOf R)} (π : ∀ n, M ⟶ Q n) [∀ n, Epi (π n)]
  (hz : ∀ n, (J ^ (n + 1)).smulι M ≫ π n = 0)
  (hex : ∀ n (W : Opens T) (s : M.val.obj (op W)), (π n).val.app (op W) s = 0 →
    s ∈ (J.powSubmodule M n).obj (op W))

omit [∀ n, Epi (π n)] in
include hex in
/-- If `π n : M ⟶ Q n` kills `J ^ (n + 1) M` and its kernel on sections is `J ^ (n + 1) M`, then
`J ^ (n + 1) M ⟶ M ⟶ Q n` is exact. -/
lemma exact_of_kernel (n : ℕ) : (ShortComplex.mk _ _ (hz n)).Exact := by
  refine sheafOfModules_exact_of_isBasis_sections _ (B := Set.univ)
    (Opens.isBasis_iff_nbhd.mpr fun {V x} hx => ⟨V, trivial, hx, le_rfl⟩) ?_
  intro V _ x hx
  exact ⟨⟨x, hex n V x hx⟩, rfl⟩

/-- If `π n : M ⟶ Q n` is an epimorphism with kernel `J ^ (n + 1) M`, then
`M / J ^ (n + 1) M ≅ Q n`. -/
def powQuotientIsoOfKernel (n : ℕ) : J.powQuotient M n ≅ Q n :=
  (colimit.isColimit _).coconePointUniqueUpToIso (J.exact_of_kernel π hz hex n).gIsCokernel

@[reassoc (attr := simp)]
lemma powQuotientπ_powQuotientIsoOfKernel_hom (n : ℕ) :
    J.powQuotientπ M n ≫ (J.powQuotientIsoOfKernel π hz hex n).hom = π n :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

variable (t : ∀ n, Q (n + 1) ⟶ Q n) (ht : ∀ n, π (n + 1) ≫ t n = π n)

/-- The cone over `n ↦ Q n` with vertex `M` given by the `π n`. -/
def coneOfπ : Cone (Functor.ofOpSequence t) where
  pt := M
  π := NatTrans.ofOpSequence (fun n => π n) (fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact (Category.id_comp _).trans (ht n).symm)

include hz hex ht in
/-- **Completeness through any presentation of the quotients.** If the `π n : M ⟶ Q n` are
epimorphisms with kernels `J ^ (n + 1) M`, compatible with maps `Q (n + 1) ⟶ Q n`, then `M` is
complete for `J` iff `M` is the limit of the `Q n`. -/
theorem isIso_toLimitPowQuotient_iff_of_kernel :
    IsIso (J.toLimitPowQuotient M) ↔ Nonempty (IsLimit (coneOfπ π t ht)) := by
  let Ψ : J.powQuotientDiagram M ⟶ Functor.ofOpSequence t :=
    NatTrans.ofOpSequence (fun n => (J.powQuotientIsoOfKernel π hz hex n).hom) (fun n => by
      rw [Functor.ofOpSequence_map_homOfLE_succ, show (J.powQuotientDiagram M).map
        (homOfLE (n.le_add_right 1)).op = J.powQuotientMap M n from
        Functor.ofOpSequence_map_homOfLE_succ _ n]
      refine (cancel_epi (J.powQuotientπ M (n + 1))).mp ?_
      exact (J.powQuotientπ_powQuotientMap_assoc M n _).trans
        ((J.powQuotientπ_powQuotientIsoOfKernel_hom π hz hex n).trans ((ht n).symm.trans
          (J.powQuotientπ_powQuotientIsoOfKernel_hom_assoc π hz hex (n + 1) (t n)).symm)))
  have : IsIso Ψ := by
    have : ∀ n : ℕᵒᵖ, IsIso (Ψ.app n) := fun ⟨n⟩ =>
      inferInstanceAs (IsIso (J.powQuotientIsoOfKernel π hz hex n).hom)
    exact NatIso.isIso_of_isIso_app _
  have e : (Cone.postcompose Ψ).obj (J.powQuotientCone M) ≅ coneOfπ π t ht :=
    Cone.ext (Iso.refl _) fun ⟨n⟩ => by
      change J.powQuotientπ M n ≫ (J.powQuotientIsoOfKernel π hz hex n).hom = 𝟙 _ ≫ π n
      exact (J.powQuotientπ_powQuotientIsoOfKernel_hom π hz hex n).trans (Category.id_comp _).symm
  constructor
  · intro hI
    exact ⟨(IsLimit.postcomposeHomEquiv (asIso Ψ) _).symm
      (J.isLimitPowQuotientConeOfIsIso M) |>.ofIsoLimit e⟩
  · rintro ⟨hc⟩
    have hc' := IsLimit.postcomposeHomEquiv (asIso Ψ) _ (hc.ofIsoLimit e.symm)
    have : J.toLimitPowQuotient M = (hc'.conePointUniqueUpToIso (limit.isLimit _)).hom := rfl
    rw [this]
    exact (hc'.conePointUniqueUpToIso (limit.isLimit _)).isIso_hom

omit [∀ n, Epi (π n)] in
/-- A morphism of modules maps `J M` into `J N`. -/
lemma map_mem_smulSubmodule {N : SheafOfModules.{u} (ringCatSheafOf R)} (g : M ⟶ N)
    {W : Opens T} {s : M.val.obj (op W)} (hs : s ∈ (J.smulSubmodule M).obj (op W)) :
    g.val.app (op W) s ∈ (J.smulSubmodule N).obj (op W) := by
  have key : ∀ {V : Opens T} {m : M.val.obj (op V)}, m ∈ J.sectionsSmul M V →
      g.val.app (op V) m ∈ J.sectionsSmul N V := fun hm => by
    refine Submodule.smul_induction_on hm (fun r hr m _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul]
      exact Submodule.smul_mem_smul hr trivial
    · rw [map_add]
      exact add_mem ha hb
  intro x hx
  obtain ⟨V, hVW, hxV, hsV⟩ := hs x hx
  refine ⟨V, hVW, hxV, ?_⟩
  have e : g.val.app (op V) (M.val.map (homOfLE hVW).op s) =
      N.val.map (homOfLE hVW).op (g.val.app (op W) s) :=
    PresheafOfModules.naturality_apply g.val (homOfLE hVW).op s
  exact e ▸ key hsV

omit [∀ n, Epi (π n)] in
/-- **Completeness is invariant under isomorphism of modules.** -/
theorem isIso_toLimitPowQuotient_of_iso {M' : SheafOfModules.{u} (ringCatSheafOf R)} (φ : M ≅ M')
    [IsIso (J.toLimitPowQuotient M)] : IsIso (J.toLimitPowQuotient M') := by
  have hz : ∀ n, (J ^ (n + 1)).smulι M' ≫ (φ.inv ≫ J.powQuotientπ M n) = 0 := fun n => by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    ext ⟨s, hs⟩
    exact J.powQuotientπ_app_eq_zero M n _ ((J ^ (n + 1)).map_mem_smulSubmodule φ.inv hs)
  have hex : ∀ n (W : Opens T) (s : M'.val.obj (op W)),
      (φ.inv ≫ J.powQuotientπ M n).val.app (op W) s = 0 → s ∈ (J.powSubmodule M' n).obj (op W) := by
    intro n W s hs
    have h1 : φ.hom.val.app (op W) (φ.inv.val.app (op W) s) ∈ (J.powSubmodule M' n).obj (op W) :=
      (J ^ (n + 1)).map_mem_smulSubmodule φ.hom
        (J.mem_powSubmodule_of_powQuotientπ_app_eq_zero M n _ hs)
    have h2 : φ.hom.val.app (op W) (φ.inv.val.app (op W) s) = s :=
      congrArg (fun k => k.val.app (op W) s) φ.inv_hom_id
    rwa [h2] at h1
  have ht : ∀ n, (φ.inv ≫ J.powQuotientπ M (n + 1)) ≫ J.powQuotientMap M n =
      φ.inv ≫ J.powQuotientπ M n := fun n => by
    rw [Category.assoc, powQuotientπ_powQuotientMap]
  refine (J.isIso_toLimitPowQuotient_iff_of_kernel (fun n => φ.inv ≫ J.powQuotientπ M n) hz hex
    (J.powQuotientMap M) ht).mpr ⟨(J.isLimitPowQuotientConeOfIsIso M).ofIsoLimit
      (Cone.ext φ fun ⟨n⟩ => ?_)⟩
  change J.powQuotientπ M n = φ.hom ≫ φ.inv ≫ J.powQuotientπ M n
  rw [φ.hom_inv_id_assoc]

end IdealSubsheaf

end Hartshorne
