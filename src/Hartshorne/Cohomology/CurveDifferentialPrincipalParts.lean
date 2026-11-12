/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.GenericDifferentials
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular
import Hartshorne.Scheme.FiniteCurveDivisorPullback
import Hartshorne.Cohomology.ProjectiveLineRegularAcyclic
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The differential principal-parts resolution of a curve

Hartshorne, *Algebraic Geometry*, III.7, the residue discussion on p. 248.

Let `X` be a nonsingular curve over an algebraically closed field `k`, with function field `K`.
Let `Ω_X = Ω_{X/k}` and let `Ω_K` be the constant sheaf with value `Ω_{K/k}`. There is a flasque
resolution

`0 → Ω_X → Ω_K → ⨁_{P closed} i_{P,*}(Ω_{K/k}/Ω_{X,P}) → 0`,

and hence `H¹(X, Ω_X)` is the cokernel of the principal-parts map on global sections.

## The objects

* `Ω_X ⟶ Ω_K` sends a section to its generic value (`Hartshorne.differentialsToGeneric`).
* `Ω_{X,P} ⊆ Ω_{K/k}` is the set of generic values of sections near `P`; it is the image of the
  stalk of `Ω_X` at `P`, and the stalk embeds.
* The direct sum is the sheaf of locally finitely supported families of principal parts
  `(ω_P mod Ω_{X,P})_P` (`Hartshorne.locallyFiniteSumSheaf`). The summand at the generic point is
  zero, and the sheaf is the coproduct of the skyscrapers over the closed points.

## The proof

* `Ω_{K/k} ≠ 0`: otherwise `K/k` would be formally unramified, hence separable algebraic, while
  `trdeg_k K = 1`.
* Injectivity: `Ω_X` is invertible (Hartshorne II.8.15). On an open set where `Ω_X ≅ 𝒪_X`
  with generator `ω₀`, a section is `a ω₀` and goes to `a_η · ω₀,η`. Here `ω₀,η ≠ 0`, since
  otherwise `d(a_η) = 0` for all functions `a`, so `Ω_{K/k} = 0`.
* Finitely many poles: every `ω ∈ Ω_{K/k}` is the generic value of a section over a nonempty open
  set `A`, so `ω ∈ Ω_{X,P}` for `P ∈ A`, and the complement of `A` is finite.
* Exactness in the middle, on stalks: a locally constant map with values in the `Ω_{X,y}` is
  constant on a connected neighbourhood. Local preimages are compatible by injectivity, and they
  glue.
* Local surjectivity: near `x`, a family of principal parts is the image of one rational
  differential with the given principal part at `x`. It suffices to remove the finitely many
  other points of the support and the poles of that differential.
* Flasqueness: `Ω_K` is constant on an irreducible space, and a locally finite sum of
  skyscrapers on a Noetherian space is flasque. The long exact sequence then identifies `H¹(X, Ω_X)`
  with the cokernel of `Γ(X, Ω_K) → Γ(X, ⨁_P i_{P,*}(Ω_{K/k}/Ω_{X,P}))`.

## Main results

* `Hartshorne.curveDifferential_principalPartsResolution`
* `Hartshorne.sheafCohomology_one_curveDifferentials_iso_cokernel`
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Hartshorne

universe u

section Nontrivial

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- On a nonsingular curve, `Ω_{K/k} ≠ 0`: otherwise `K/k` would be formally unramified, hence
algebraic, while `trdeg_k K = 1`. -/
theorem functionFieldDifferentials_nontrivial (hX : X.IsNonsingularCurve k) :
    Nontrivial (functionFieldDifferentials (X ↘ Spec (.of k))) := by
  set f := X ↘ Spec (.of k)
  have hf : FiniteType f := ⟨hX.locallyOfFiniteType, hX.quasiCompact⟩
  let _ : LocallyOfFiniteType f := hf.1
  let := functionFieldAlgebra f
  obtain ⟨z, hz⟩ := hX.exists_ne_genericPoint
  have hzc : IsClosed ({z} : Set X) :=
    (hX.isClosed_singleton_iff_coheight_eq_one z).2 ((hX.coheight_eq_one_iff z).2 hz)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨d, -, htr, hdim⟩ := exists_dim_eq_trdeg_of_isAffineOpen f hf U hU
  have hn : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by
    simpa using hX.topologicalKrullDim_eq_one
  have h1 := DifferentialsNonsingular.ringKrullDim_stalk_of_isClosed f hf hn z hzc
  rw [hdim ⟨z, hzU⟩ hzc] at h1
  have hd : d = 1 := by exact_mod_cast h1
  have hUle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let φU : k →+* Γ(X, U) :=
    (f.appLE ⊤ U hUle).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k Γ(X, U) := φU.toAlgebra
  have hinv : Function.Surjective (Scheme.ΓSpecIso (.of k)).inv := by
    intro w
    exact ⟨(Scheme.ΓSpecIso (.of k)).hom w, by simp⟩
  have hφU : φU.FiniteType :=
    (f.finiteType_appLE (isAffineOpen_top _) hU hUle).comp
      (RingHom.FiniteType.of_surjective _ hinv)
  have : Algebra.FiniteType k Γ(X, U) := hφU
  have : IsScalarTower k Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change X.presheaf.germ (f ⁻¹ᵁ ⊤) (genericPoint X) trivial
          (f.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv a)) = X.germToFunctionField U (φU a)
      simp only [φU, RingHom.coe_comp, Function.comp_apply]
      convert
        (X.presheaf.germ_res_apply (homOfLE hUle) (genericPoint X)
          (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
            (by simpa using (inferInstance : Nonempty U)))
          (f.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv a))).symm using 1
      simp [Scheme.Hom.appLE, Scheme.germToFunctionField, Scheme.functionField]
      rfl
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    .of_isLocalization _ (nonZeroDivisors Γ(X, U))
  have : Algebra.EssFiniteType k X.functionField := .comp k Γ(X, U) X.functionField
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have : Algebra.FormallyUnramified k X.functionField := ⟨hsub⟩
  have : Algebra.IsSeparable k X.functionField :=
    Algebra.FormallyUnramified.isSeparable k X.functionField
  have h0 : Algebra.trdeg k X.functionField = 0 := trdeg_eq_zero
  rw [htr, hd] at h0
  exact one_ne_zero h0

end Nontrivial

/-- The structure sheaf of a scheme, as a module over itself. -/
abbrev unitModuleOf (Y : Scheme.{u}) : Y.Modules :=
  SheafOfModules.unit Y.ringCatSheaf

section Injective

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
  (W : X.Opens)
  (β : (Scheme.relativeDifferentials f).restrict W.ι ≅
    unitModuleOf W.toScheme)

/-- The unit section of the structure sheaf over `V`, as a section of a module. -/
def unitModuleSection {Y : Scheme.{u}} (V : Y.Opens) : Γ(unitModuleOf Y, V) :=
  (1 : Γ(Y, V))

/-- A section of the structure sheaf, regarded as a section of a module, as a function. -/
def unitModuleSectionVal {Y : Scheme.{u}} {V : Y.Opens} (a : Γ(unitModuleOf Y, V)) : Γ(Y, V) :=
  a

theorem smul_unitModuleSection {Y : Scheme.{u}} {V : Y.Opens} (a : Γ(unitModuleOf Y, V)) :
    unitModuleSectionVal a • unitModuleSection V = a :=
  mul_one (unitModuleSectionVal a)

theorem unitModuleSection_res {Y : Scheme.{u}} {V V' : Y.Opens} (i : V' ⟶ V) :
    (unitModuleOf Y).presheaf.map i.op (unitModuleSection V) = unitModuleSection V' :=
  map_one (Y.presheaf.map i.op).hom

/-- A generator of `Ω_{X/k}` over an open set `W` on which it is trivialized. -/
def localGenerator : Γ(Scheme.relativeDifferentials f, W.ι ''ᵁ ⊤) :=
  β.inv.app ⊤ (unitModuleSection ⊤)

omit [IsIntegral X] in
theorem ι_image_le_ι_image_top (V : W.toScheme.Opens) : W.ι ''ᵁ V ≤ W.ι ''ᵁ ⊤ :=
  W.ι.image_mono le_top

omit [IsIntegral X] in
/-- Over an open subset of `W`, every section of `Ω_{X/k}` is a multiple of the generator. -/
theorem eq_smul_localGenerator (V : W.toScheme.Opens)
    (s : Γ(Scheme.relativeDifferentials f, W.ι ''ᵁ V)) :
    s = (W.ι.appIso V).inv (unitModuleSectionVal (β.hom.app V s)) •
      (Scheme.relativeDifferentials f).presheaf.map (homOfLE (ι_image_le_ι_image_top W V)).op
        (localGenerator f W β) := by
  have h1 : β.inv.app V (β.hom.app V s) = s :=
    congrArg (fun φ => (Scheme.Modules.Hom.app φ V) s) β.hom_inv_id
  have h4 := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf β.inv).naturality (homOfLE (le_top : V ≤ ⊤)).op)
    (unitModuleSection ⊤)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, unitModuleSection_res] at h4
  show @Eq Γ((Scheme.relativeDifferentials f).restrict W.ι, V) s _
  refine h1.symm.trans ?_
  conv_lhs => rw [← smul_unitModuleSection (β.hom.app V s)]
  rw [Scheme.Modules.Hom.app_smul]
  erw [h4]
  rfl

/-- The image of a section over an open subset of `W` is a multiple of that of the generator. -/
theorem differentialsGenericValue_eq_smul (V : W.toScheme.Opens)
    (s : Γ(Scheme.relativeDifferentials f, W.ι ''ᵁ V)) (y : W.ι ''ᵁ V) :
    differentialsGenericValue f s y =
      genericGerm _ y ((W.ι.appIso V).inv (unitModuleSectionVal (β.hom.app V s))) •
        differentialsGenericValue f (localGenerator f W β)
          ⟨y.1, ι_image_le_ι_image_top W V y.2⟩ := by
  conv_lhs => rw [eq_smul_localGenerator f W β V s]
  rw [differentialsToGeneric_smul, differentialsToGeneric_res]

omit [IsIntegral X] in
theorem mem_of_mem_ι_image_top {y : X} (hy : y ∈ W.ι ''ᵁ ⊤) : y ∈ W := by
  rwa [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at hy

/-- The image of the generator in `Ω_{K/k}` is nonzero. -/
theorem differentialsGenericValue_localGenerator_ne_zero
    [Nontrivial (functionFieldDifferentials f)] (y : W.ι ''ᵁ ⊤) :
    differentialsGenericValue f (localGenerator f W β) y ≠ 0 := by
  intro h0
  have hD : ∀ (V : W.toScheme.Opens) (a : Γ(X, W.ι ''ᵁ V)) (z : W.ι ''ᵁ V),
      functionFieldD f (genericGerm _ z a) = 0 := by
    intro V a z
    refine (differentialsToGeneric_d f _ a z).symm.trans
      ((differentialsGenericValue_eq_smul f W β V _ z).trans ?_)
    rw [differentialsGenericValue_eq f _ _ y, h0, smul_zero]
  have hK : ∀ z : X.functionField, functionFieldD f z = 0 := by
    intro z
    obtain ⟨W', hW', e, rfl⟩ := X.presheaf.exists_germ_eq z
    have hmem : genericPoint X ∈ W.ι ''ᵁ (W.ι ⁻¹ᵁ W') := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact ⟨genericPoint_mem_of_mem (mem_of_mem_ι_image_top W y.2), hW'⟩
    have h := hD _ (X.presheaf.map (homOfLE (W.ι.image_preimage_le W')).op e) ⟨_, hmem⟩
    rwa [genericGerm_res] at h
  have hle : Submodule.span X.functionField (Set.range (functionFieldD f)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact hK z
  rw [span_range_functionFieldD, top_le_iff] at hle
  obtain ⟨a, ha⟩ := exists_ne (0 : functionFieldDifferentials f)
  exact ha ((Submodule.mem_bot _).1 (hle.symm ▸ Submodule.mem_top))

include β in
/-- Over a nonempty open subset of a trivializing open set, `Ω_{X/k} ⟶ Ω_K` is injective. -/
theorem differentialsToGeneric_app_injective_of_iso [Nontrivial (functionFieldDifferentials f)]
    (V : W.toScheme.Opens) (y₀ : W.ι ''ᵁ V) :
    Function.Injective ((differentialsToGeneric f).app (W.ι ''ᵁ V)).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hval : differentialsGenericValue f s y₀ = 0 := by
    have h : differentialsGenericValue f s = 0 := hs
    rw [h]
    rfl
  rw [differentialsGenericValue_eq_smul f W β V s y₀] at hval
  have hgerm := (smul_eq_zero.1 hval).resolve_right
    (differentialsGenericValue_localGenerator_ne_zero f W β _)
  have hr : (W.ι.appIso V).inv (unitModuleSectionVal (β.hom.app V s)) = 0 :=
    germ_injective_of_isIntegral X _ _ (hgerm.trans (map_zero _).symm)
  rw [eq_smul_localGenerator f W β V s, hr, zero_smul]

end Injective

section GlobalInjective

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))

/-- A trivialization of an invertible module identifies its restriction with the structure
sheaf. -/
noncomputable def restrictIsoUnitOfFree {M : X.Modules} {W : X.Opens}
    (α : M.restrict W.ι ≅ SheafOfModules.free (ULift.{u} (Fin 1))) :
    M.restrict W.ι ≅ unitModuleOf W.toScheme :=
  α ≪≫ Limits.coproductUniqueIso (C := SheafOfModules W.toScheme.ringCatSheaf)
    (fun _ : ULift.{u} (Fin 1) => SheafOfModules.unit W.toScheme.ringCatSheaf)

/-- **Injectivity of `Ω_{X/k} ⟶ Ω_K`** on every open set, for `Ω_{X/k}` invertible and
`Ω_{K/k} ≠ 0`. -/
theorem differentialsToGeneric_app_injective [Nontrivial (functionFieldDifferentials f)]
    (hfree : (Scheme.relativeDifferentials f).IsLocallyFreeOfRank 1) (U : X.Opens) :
    Function.Injective ((differentialsToGeneric f).app U).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  choose W hW α using hfree
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj (Scheme.relativeDifferentials f)
  let Ui : U → X.Opens := fun x => (W x).ι ''ᵁ ((W x).ι ⁻¹ᵁ U)
  have hUi : ∀ x, Ui x ≤ U := fun x => (W x).ι.image_preimage_le U
  refine TopCat.Sheaf.eq_of_locally_eq' F Ui U (fun x => homOfLE (hUi x)) ?_ s 0 fun x => ?_
  · intro y hy
    refine Opens.mem_iSup.2 ⟨⟨y, hy⟩, ?_⟩
    change y ∈ (W y).ι ''ᵁ ((W y).ι ⁻¹ᵁ U)
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨hW y, hy⟩
  · have hx : (x : X) ∈ Ui x := by
      change (x : X) ∈ (W x).ι ''ᵁ ((W x).ι ⁻¹ᵁ U)
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact ⟨hW x, x.2⟩
    rw [map_zero]
    refine differentialsToGeneric_app_injective_of_iso f (W x)
      (restrictIsoUnitOfFree (α x).some) _ ⟨x, hx⟩ ?_
    have h := ConcreteCategory.congr_hom
      ((Scheme.Modules.Hom.mapPresheaf (differentialsToGeneric f)).naturality
        (homOfLE (hUi x)).op) s
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    refine (h.trans ?_).trans (map_zero ((differentialsToGeneric f).app _).hom).symm
    change (genericConstantModule (functionFieldDifferentials f)).presheaf.map _
      (((differentialsToGeneric f).app U).hom s) = 0
    rw [hs, map_zero]

end GlobalInjective

section Topology

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- On a curve, every point other than the generic point is closed. -/
theorem isClosed_singleton_of_ne_genericPoint (hX : X.IsNonsingularCurve k) {x : X}
    (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) :=
  (hX.isClosed_singleton_iff_coheight_eq_one x).2 ((hX.coheight_eq_one_iff x).2 hx)

/-- On a curve, a closed set not containing the generic point is finite. -/
theorem finite_of_isClosed_of_genericPoint_notMem (hX : X.IsNonsingularCurve k) {Z : Set X}
    (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by
  have : IsNoetherian X := hX.satisfiesConditionStar.isNoetherian
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSf.sUnion fun t ht => ?_
  obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  have hzt : z ∈ t := hz.mem
  have hzη : z ≠ genericPoint X := fun h => hη ⟨t, ht, h ▸ hzt⟩
  have : t = {z} := by
    rw [← hz.def, (isClosed_singleton_of_ne_genericPoint hX hzη).closure_eq]
  rw [this]
  exact Set.finite_singleton z

/-- On a curve, the complement of a nonempty open set is finite. -/
theorem finite_compl_of_isNonsingularCurve (hX : X.IsNonsingularCurve k) (U : X.Opens)
    (hU : Nonempty U) :
    ((U : Set X)ᶜ).Finite := by
  obtain ⟨x⟩ := hU
  exact finite_of_isClosed_of_genericPoint_notMem hX U.isOpen.isClosed_compl
    fun h => h (genericPoint_mem_of_mem x.2)

/-- On a curve, a finite set of points other than the generic point is closed. -/
theorem isClosed_of_finite_of_genericPoint_notMem (hX : X.IsNonsingularCurve k) {Z : Set X}
    (hZ : Z.Finite) (hη : genericPoint X ∉ Z) : IsClosed Z := by
  rw [← Set.biUnion_of_singleton Z]
  exact hZ.isClosed_biUnion fun x hx =>
    isClosed_singleton_of_ne_genericPoint hX fun h => hη (h ▸ hx)

end Topology

section StalkRange

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))

theorem differentialsGenericValue_neg {U : X.Opens} (s : Γ(Scheme.relativeDifferentials f, U))
    (y : U) : differentialsGenericValue f (-s) y = -differentialsGenericValue f s y := by
  have h := map_neg ((differentialsToGeneric f).app U).hom s
  exact congrArg (fun m => (show LocallyConstant U (functionFieldDifferentials f) from m) y) h

/-- **The stalk `Ω_{X,P}` inside `Ω_{K/k}`**: the generic values of sections of `Ω_{X/k}` over
open neighbourhoods of `P`. It is the image of the stalk of `Ω_{X/k}` at `P`
(`range_differentialsStalkToGeneric`), which embeds into `Ω_{K/k}` on a nonsingular curve. -/
def differentialsStalkRange (P : X) : AddSubgroup (functionFieldDifferentials f) where
  carrier := {ω | ∃ (U : X.Opens) (hP : P ∈ U) (s : Γ(Scheme.relativeDifferentials f, U)),
    differentialsGenericValue f s ⟨P, hP⟩ = ω}
  zero_mem' := ⟨⊤, trivial, 0, differentialsGenericValue_zero f _⟩
  add_mem' := by
    rintro _ _ ⟨U₁, h₁, s₁, rfl⟩ ⟨U₂, h₂, s₂, rfl⟩
    refine ⟨U₁ ⊓ U₂, ⟨h₁, h₂⟩,
      (Scheme.relativeDifferentials f).presheaf.map (homOfLE inf_le_left).op s₁ +
        (Scheme.relativeDifferentials f).presheaf.map (homOfLE inf_le_right).op s₂, ?_⟩
    rw [differentialsGenericValue_add, differentialsToGeneric_res, differentialsToGeneric_res]
  neg_mem' := by
    rintro _ ⟨U, h, s, rfl⟩
    exact ⟨U, h, -s, differentialsGenericValue_neg f s _⟩

theorem differentialsGenericValue_mem {U : X.Opens} (s : Γ(Scheme.relativeDifferentials f, U))
    (y : U) : differentialsGenericValue f s y ∈ differentialsStalkRange f y.1 :=
  ⟨U, y.2, s, rfl⟩

/-- At the generic point, every rational differential is regular. -/
theorem differentialsStalkRange_genericPoint :
    differentialsStalkRange f (genericPoint X) = ⊤ := by
  refine eq_top_iff.2 fun ω _ => ?_
  obtain ⟨U, ⟨x⟩, s, hs⟩ := exists_differentialsToGeneric_eq f ω
  have hη : genericPoint X ∈ U := genericPoint_mem_of_mem x.2
  exact ⟨U, hη, s, hs _⟩

/-- The stalk map `(Ω_{X/k})_P → Ω_{K/k}`, induced by the generic values of sections. -/
noncomputable def differentialsStalkToGeneric (P : X) :
    (Scheme.relativeDifferentials f).presheaf.stalk P ⟶
      AddCommGrpCat.of (functionFieldDifferentials f) :=
  Limits.colimit.desc ((OpenNhds.inclusion P).op ⋙ (Scheme.relativeDifferentials f).presheaf)
    { pt := AddCommGrpCat.of (functionFieldDifferentials f)
      ι :=
        { app U := AddCommGrpCat.ofHom
            { toFun s := differentialsGenericValue f (U := U.unop.1) s ⟨P, U.unop.2⟩
              map_zero' := differentialsGenericValue_zero f _
              map_add' s t := differentialsGenericValue_add f s t _ }
          naturality U V i := by
            ext s
            exact differentialsToGeneric_res f i.unop s _ } }

theorem differentialsStalkToGeneric_germ (P : X) {U : X.Opens} (hP : P ∈ U)
    (s : Γ(Scheme.relativeDifferentials f, U)) :
    differentialsStalkToGeneric f P ((Scheme.relativeDifferentials f).presheaf.germ U P hP s) =
      differentialsGenericValue f s ⟨P, hP⟩ := by
  rw [TopCat.Presheaf.germ, differentialsStalkToGeneric]
  erw [← ConcreteCategory.comp_apply, Limits.colimit.ι_desc]
  rfl

/-- `Ω_{X,P}` is the image of the stalk. -/
theorem range_differentialsStalkToGeneric (P : X) :
    (differentialsStalkToGeneric f P).hom.range = differentialsStalkRange f P := by
  ext ω
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨U, hP, s, rfl⟩ := (Scheme.relativeDifferentials f).presheaf.exists_germ_eq t
    exact ⟨U, hP, s, (differentialsStalkToGeneric_germ f P hP s).symm⟩
  · rintro ⟨U, hP, s, rfl⟩
    exact ⟨_, differentialsStalkToGeneric_germ f P hP s⟩

/-- On a nonsingular curve the stalk of `Ω_{X/k}` embeds into `Ω_{K/k}`. -/
theorem differentialsStalkToGeneric_injective [Nontrivial (functionFieldDifferentials f)]
    (hfree : (Scheme.relativeDifferentials f).IsLocallyFreeOfRank 1) (P : X) :
    Function.Injective (differentialsStalkToGeneric f P) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨U, hP, s, rfl⟩ := (Scheme.relativeDifferentials f).presheaf.exists_germ_eq t
  rw [differentialsStalkToGeneric_germ] at ht
  have hs : differentialsGenericValue f s = 0 :=
    LocallyConstant.ext fun y => (differentialsGenericValue_eq f s y ⟨P, hP⟩).trans ht
  rw [differentialsToGeneric_app_injective f hfree U (hs.trans (map_zero _).symm), map_zero]

end StalkRange

section Resolution

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X]

/-- The sheaf of differentials `Ω_X = Ω_{X/k}`, as a sheaf of abelian groups. -/
abbrev curveDifferentialsSheaf : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (Scheme.relativeDifferentials (X ↘ Spec (.of k)))

/-- The constant sheaf `Ω_K` with value `Ω_{K/k}`. -/
abbrev rationalDifferentialsSheaf : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
  constantSheaf X.toTopCat (AddCommGrpCat.of (functionFieldDifferentials (X ↘ Spec (.of k))))

/-- The group `Ω_{K/k}/Ω_{X,P}` of differential principal parts at `P`. -/
abbrev differentialPrincipalPartsGroup (P : X) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of
    (functionFieldDifferentials (X ↘ Spec (.of k)) ⧸ differentialsStalkRange (X ↘ Spec (.of k)) P)

/-- The sheaf `⨁_P i_{P,*}(Ω_{K/k}/Ω_{X,P})` of locally finitely supported families of
differential principal parts. -/
abbrev differentialPrincipalPartsSheaf : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
  locallyFiniteSumSheaf (X := X.toTopCat) (differentialPrincipalPartsGroup k X)

/-- The map `Ω_X ⟶ Ω_K`, sending a section to its generic value. -/
def differentialsToRational : curveDifferentialsSheaf k X ⟶ rationalDifferentialsSheaf k X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map (differentialsToGeneric (X ↘ Spec (.of k)))

variable {k X}

/-- A rational differential has finitely many poles: the principal parts of a locally constant
map to `Ω_{K/k}` have locally finite support. -/
theorem locallyFiniteSupport_differentialPrincipalPart (hX : X.IsNonsingularCurve k)
    {U : X.Opens} (s : LocallyConstant U (functionFieldDifferentials (X ↘ Spec (.of k)))) :
    LocallyFiniteSupport (X := X.toTopCat) (differentialPrincipalPartsGroup k X)
      (fun x : U => (QuotientAddGroup.mk (s x) : differentialPrincipalPartsGroup k X x.1)) := by
  intro x
  obtain ⟨A, ⟨a⟩, t, ht⟩ := exists_differentialsToGeneric_eq (X ↘ Spec (.of k)) (s x)
  let W : Set U := s ⁻¹' {s x}
  have hW : IsOpen W := s.isLocallyConstant.isOpen_fiber _
  let V : X.Opens := ⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hW⟩
  refine ⟨V, ⟨x, rfl, rfl⟩, ?_⟩
  refine ((finite_compl_of_isNonsingularCurve hX A ⟨a⟩).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro y ⟨⟨w, hwW, hwy⟩, hy⟩ hyA
  apply hy
  have hwy' : w = y := Subtype.ext hwy
  subst hwy'
  rw [QuotientAddGroup.eq_zero_iff]
  have hsw : s w = s x := hwW
  rw [hsw, ← ht ⟨w.1, hyA⟩]
  exact differentialsGenericValue_mem _ t ⟨w.1, hyA⟩

/-- **The principal-parts map `Ω_K ⟶ ⨁_P i_{P,*}(Ω_{K/k}/Ω_{X,P})`**: a locally constant map
`s : U → Ω_{K/k}` goes to the family of its principal parts `(s(P) mod Ω_{X,P})_{P ∈ U}`. -/
def rationalToPrincipalParts (hX : X.IsNonsingularCurve k) :
    rationalDifferentialsSheaf k X ⟶ differentialPrincipalPartsSheaf k X :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun s => ⟨fun x : U.unop =>
              (QuotientAddGroup.mk (s x) : differentialPrincipalPartsGroup k X x.1),
            locallyFiniteSupport_differentialPrincipalPart hX s⟩
          map_zero' := Subtype.ext (funext fun _ => QuotientAddGroup.mk_zero _)
          map_add' := fun _ _ => Subtype.ext (funext fun _ => QuotientAddGroup.mk_add _ _ _) }
      naturality := fun _ _ _ => rfl }

theorem differentialsToRational_comp_rationalToPrincipalParts (hX : X.IsNonsingularCurve k) :
    differentialsToRational k X ≫ rationalToPrincipalParts hX = 0 := by
  apply ObjectProperty.hom_ext
  ext U s
  apply Subtype.ext
  funext x
  exact (QuotientAddGroup.eq_zero_iff _).2 (differentialsGenericValue_mem _ s x)

/-- **The differential principal-parts complex**
`Ω_X ⟶ Ω_K ⟶ ⨁_P i_{P,*}(Ω_{K/k}/Ω_{X,P})`. -/
def differentialPrincipalPartsComplex (hX : X.IsNonsingularCurve k) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat) :=
  ShortComplex.mk (differentialsToRational k X) (rationalToPrincipalParts hX)
    (differentialsToRational_comp_rationalToPrincipalParts hX)

/-- On a nonsingular curve over an algebraically closed field, `Ω_{X/k}` is invertible
(Hartshorne II.8.15). -/
theorem relativeDifferentials_isLocallyFreeOfRank_one [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) :
    (Scheme.relativeDifferentials (X ↘ Spec (.of k))).IsLocallyFreeOfRank 1 := by
  have : IsNoetherian X := hX.satisfiesConditionStar.isNoetherian
  have hf : FiniteType (X ↘ Spec (.of k)) := ⟨hX.locallyOfFiniteType, hX.quasiCompact⟩
  have hn : topologicalKrullDim X = ((1 : ℕ) : WithBot ℕ∞) := by
    simpa using hX.topologicalKrullDim_eq_one
  exact (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank _ hf 1 hn).1
    ⟨inferInstance, hX.isRegularLocalRing_stalk⟩

/-- `Ω_X ⟶ Ω_K` is a monomorphism. -/
theorem mono_differentialsToRational [IsAlgClosed k] (hX : X.IsNonsingularCurve k) :
    Mono (differentialsToRational k X) := by
  have := functionFieldDifferentials_nontrivial hX
  have hU : ∀ U, Mono ((differentialsToRational k X).hom.app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).2 (differentialsToGeneric_app_injective _
      (relativeDifferentials_isLocallyFreeOfRank_one hX) U.unop)
  have : Mono (differentialsToRational k X).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- **Gluing local representatives.** A locally constant map to `Ω_{K/k}` whose values lie in
the stalks `Ω_{X,y}` is the image of a section of `Ω_X`. -/
theorem exists_differentialsGenericValue_eq [IsAlgClosed k] (hX : X.IsNonsingularCurve k)
    {W : X.Opens} (s : LocallyConstant W (functionFieldDifferentials (X ↘ Spec (.of k))))
    (hs : ∀ y : W, s y ∈ differentialsStalkRange (X ↘ Spec (.of k)) y.1) :
    ∃ t : Γ(Scheme.relativeDifferentials (X ↘ Spec (.of k)), W),
      differentialsGenericValue _ t = s := by
  have := functionFieldDifferentials_nontrivial hX
  have hfree := relativeDifferentials_isLocallyFreeOfRank_one hX
  by_cases hW : Nonempty W
  · obtain ⟨y₀⟩ := hW
    have hpre : PreconnectedSpace W := Subtype.preconnectedSpace
      ((PreirreducibleSpace.isPreirreducible_univ (X := X)).open_subset W.isOpen
        (Set.subset_univ _)).isPreconnected
    have hconst : ∀ y : W, s y = s y₀ := fun y =>
      s.isLocallyConstant.apply_eq_of_preconnectedSpace y y₀
    choose U hyU t ht using fun y : W => hs y
    let B : W → X.Opens := fun y => U y ⊓ W
    let F := curveDifferentialsSheaf k X
    let sf : ∀ y : W, ToType (F.obj.obj (op (B y))) := fun y =>
      (Scheme.relativeDifferentials (X ↘ Spec (.of k))).presheaf.map (homOfLE inf_le_left).op (t y)
    have hval : ∀ (y : W) (V : X.Opens) (i : V ⟶ B y) (z : V),
        differentialsGenericValue _
          ((Scheme.relativeDifferentials (X ↘ Spec (.of k))).presheaf.map i.op (sf y)) z =
          s y₀ := by
      intro y V i z
      rw [differentialsToGeneric_res, differentialsToGeneric_res,
        differentialsGenericValue_eq _ _ _ ⟨y.1, hyU y⟩, ht y, hconst y]
    have hcompat : TopCat.Presheaf.IsCompatible F.obj B sf := by
      intro y z
      apply differentialsToGeneric_app_injective _ hfree
      refine LocallyConstant.ext fun p => ?_
      exact (hval y _ _ p).trans (hval z _ _ p).symm
    obtain ⟨t', ht', -⟩ := TopCat.Sheaf.existsUnique_gluing' F B W
      (fun y => homOfLE inf_le_right) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyU _, hy⟩) sf
      hcompat
    refine ⟨t', LocallyConstant.ext fun y => ?_⟩
    have h1 := differentialsToGeneric_res _ (homOfLE (inf_le_right : B y ≤ W)) t'
      ⟨y.1, hyU y, y.2⟩
    have h2 : (Scheme.relativeDifferentials (X ↘ Spec (.of k))).presheaf.map
        (homOfLE inf_le_right).op t' =
        sf y := ht' y
    rw [h2] at h1
    refine h1.symm.trans (Eq.trans ?_ (hconst y).symm)
    have h3 := hval y (B y) (𝟙 _) ⟨y.1, hyU y, y.2⟩
    rwa [op_id, (Scheme.relativeDifferentials (X ↘ Spec (.of k))).presheaf.map_id,
      ConcreteCategory.id_apply] at h3
  · exact ⟨0, LocallyConstant.ext fun y => (hW ⟨y⟩).elim⟩

/-- **Exactness at `Ω_K`**, checked on stalks. -/
theorem differentialPrincipalPartsComplex_exact [IsAlgClosed k] (hX : X.IsNonsingularCurve k) :
    (differentialPrincipalPartsComplex hX).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro t ht
  obtain ⟨U, hxU, s, rfl⟩ := (rationalDifferentialsSheaf k X).presheaf.exists_germ_eq t
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (rationalToPrincipalParts hX).hom
    ((rationalDifferentialsSheaf k X).presheaf.germ U x hxU s) = 0 at ht
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ht
  have ht' : (differentialPrincipalPartsSheaf k X).presheaf.germ U x hxU
      ((rationalToPrincipalParts hX).hom.app (op U) s) =
      (differentialPrincipalPartsSheaf k X).presheaf.germ U x hxU 0 := by
    rw [ht]
    exact (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ :=
    (differentialPrincipalPartsSheaf k X).presheaf.germ_eq x hxU hxU _ _ ht'
  rw [map_zero] at hW
  let sW : LocallyConstant W (functionFieldDifferentials (X ↘ Spec (.of k))) :=
    (rationalDifferentialsSheaf k X).presheaf.map iU.op s
  have hsW : (rationalToPrincipalParts hX).hom.app (op W) sW = 0 := by
    rw [← hW]
    exact (ConcreteCategory.congr_hom ((rationalToPrincipalParts hX).hom.naturality iU.op) s)
  have hmem : ∀ y : W, sW y ∈ differentialsStalkRange _ y.1 := by
    intro y
    have hy := congrFun (congrArg Subtype.val hsW) y
    exact (QuotientAddGroup.eq_zero_iff _).1 hy
  obtain ⟨r, hr⟩ := exists_differentialsGenericValue_eq hX sW hmem
  refine ⟨(curveDifferentialsSheaf k X).presheaf.germ W x hxW r, ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := (curveDifferentialsSheaf k X).presheaf)
    (G := (rationalDifferentialsSheaf k X).presheaf) W x hxW
    (differentialsToRational k X).hom r).trans ?_
  change (rationalDifferentialsSheaf k X).presheaf.germ W x hxW (differentialsGenericValue _ r) = _
  rw [hr]
  exact (rationalDifferentialsSheaf k X).presheaf.germ_res_apply iU x hxW s

/-- The principal parts at the generic point vanish. -/
theorem differentialPrincipalPartsGroup_genericPoint_eq_zero
    (a : differentialPrincipalPartsGroup k X (genericPoint X)) : a = 0 := by
  obtain ⟨ω, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [QuotientAddGroup.eq_zero_iff, differentialsStalkRange_genericPoint]
  exact AddSubgroup.mem_top ω

/-- **Local surjectivity of the principal-parts map**: near a point `x`, a family of principal
parts is the image of a single rational differential with the prescribed principal part at `x`,
on a neighbourhood avoiding the other points of the support and the poles of that differential. -/
theorem epi_rationalToPrincipalParts (hX : X.IsNonsingularCurve k) :
    Epi (rationalToPrincipalParts hX) := by
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi, TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hxU
  classical
  obtain ⟨ω, hω⟩ := QuotientAddGroup.mk_surjective (t.1 ⟨x, hxU⟩)
  obtain ⟨A, ⟨a⟩, r, hr⟩ := exists_differentialsToGeneric_eq (X ↘ Spec (.of k)) ω
  obtain ⟨V₀, hxV₀, hfin⟩ := t.2 ⟨x, hxU⟩
  let E : Set X := ((Subtype.val '' {y : U | y.1 ∈ V₀ ∧ t.1 y ≠ 0}) ∪ (A : Set X)ᶜ) \ {x}
  have hEfin : E.Finite :=
    ((hfin.image _).union (finite_compl_of_isNonsingularCurve hX A ⟨a⟩)).sdiff
  have hηA : genericPoint X ∈ A := genericPoint_mem_of_mem a.2
  have hηE : genericPoint X ∉ E := by
    rintro ⟨h | h, -⟩
    · obtain ⟨⟨y, hyU⟩, ⟨-, hy⟩, hyη⟩ := h
      change y = genericPoint X at hyη
      subst hyη
      exact hy (differentialPrincipalPartsGroup_genericPoint_eq_zero _)
    · exact h hηA
  have hEc : IsClosed E := isClosed_of_finite_of_genericPoint_notMem hX hEfin hηE
  let V : X.Opens := U ⊓ V₀ ⊓ ⟨Eᶜ, hEc.isOpen_compl⟩
  refine ⟨V, fun y hy => hy.1.1, ⟨LocallyConstant.const V ω, ?_⟩, ⟨⟨hxU, hxV₀⟩, fun h => h.2 rfl⟩⟩
  apply Subtype.ext
  funext y
  obtain ⟨y, ⟨⟨hyU, hyV₀⟩, hyE⟩⟩ := y
  change (QuotientAddGroup.mk ω : differentialPrincipalPartsGroup k X y) = t.1 ⟨y, hyU⟩
  by_cases hyx : y = x
  · subst hyx
    exact hω
  · have hyA : y ∈ A := by
      by_contra h
      exact hyE ⟨Or.inr h, hyx⟩
    have ht0 : t.1 ⟨y, hyU⟩ = 0 := by
      by_contra h
      exact hyE ⟨Or.inl ⟨⟨y, hyU⟩, ⟨hyV₀, h⟩, rfl⟩, hyx⟩
    rw [ht0, QuotientAddGroup.eq_zero_iff, ← hr ⟨y, hyA⟩]
    exact differentialsGenericValue_mem _ r ⟨y, hyA⟩

/-- The differential principal-parts complex is a short exact sequence. -/
theorem differentialPrincipalPartsComplex_shortExact [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) : (differentialPrincipalPartsComplex hX).ShortExact :=
  { exact := differentialPrincipalPartsComplex_exact hX
    mono_f := mono_differentialsToRational hX
    epi_g := epi_rationalToPrincipalParts hX }

/-- `Ω_K` is flasque, being a constant sheaf on an irreducible space. -/
theorem isFlasque_rationalDifferentialsSheaf : (rationalDifferentialsSheaf k X).IsFlasque :=
  have : IrreducibleSpace X.toTopCat := inferInstanceAs (IrreducibleSpace X)
  isFlasque_constantSheaf_of_irreducibleSpace X.toTopCat _

/-- The sum of skyscrapers `⨁_P i_{P,*}(Ω_{K/k}/Ω_{X,P})` is flasque, `X` being Noetherian. -/
theorem isFlasque_differentialPrincipalPartsSheaf (hX : X.IsNonsingularCurve k) :
    (differentialPrincipalPartsSheaf k X).IsFlasque :=
  have : IsNoetherian X := hX.satisfiesConditionStar.isNoetherian
  have : NoetherianSpace X.toTopCat := inferInstanceAs (NoetherianSpace X)
  isFlasque_locallyFiniteSumSheaf _

/-- **`H¹(X, Ω_X)` is the cokernel of the principal-parts map on global sections**
`Γ(X, Ω_K) → Γ(X, ⨁_P i_{P,*}(Ω_{K/k}/Ω_{X,P}))`, by the long exact cohomology sequence of the
flasque resolution. -/
theorem sheafCohomology_one_curveDifferentials_iso_cokernel [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) :
    Nonempty ((sheafCohomology X.toTopCat 1).obj (curveDifferentialsSheaf k X) ≅
      Limits.cokernel ((rationalToPrincipalParts hX).hom.app (op ⊤))) := by
  have hS := differentialPrincipalPartsComplex_shortExact hX
  set S := differentialPrincipalPartsComplex hX
  have : S.X₂.IsFlasque := isFlasque_rationalDifferentialsSheaf
  have hδ : Epi (sheafCohomologyδ hS 0) :=
    (sheafCohomology_exact₁ hS 0).epi_f
      ((sheafCohomology_isZero_of_isFlasque S.X₂ 0).eq_of_tgt _ _)
  have hcok := (sheafCohomology_exact₃ hS 0).gIsCokernel
  let e₁ := IsColimit.coconePointUniqueUpToIso hcok
    (Limits.cokernelIsCokernel ((sheafCohomology X.toTopCat 0).map S.g))
  let e₂ : Limits.cokernel ((sheafCohomology X.toTopCat 0).map S.g) ≅
      Limits.cokernel ((sheafSectionsOver (X := X.toTopCat) ⊤).map S.g) :=
    Limits.cokernel.mapIso _ _ ((sheafCohomologyZeroIso X.toTopCat).app S.X₂)
      ((sheafCohomologyZeroIso X.toTopCat).app S.X₃)
      ((sheafCohomologyZeroIso X.toTopCat).hom.naturality S.g)
  exact ⟨e₁ ≪≫ e₂⟩

end Resolution

section ClosedPoints

/-- A colimit cofan whose summands outside `p` are zero restricts to a colimit cofan indexed by
the indices satisfying `p`. -/
def isColimitCofanSubtypeOfIsZero {C : Type*} [Category C] {ι : Type*} {F : ι → C}
    {c : Cofan F} (hc : IsColimit c) (p : ι → Prop) (hz : ∀ i, ¬ p i → IsZero (F i)) :
    IsColimit (Cofan.mk c.pt (fun j : {i // p i} => c.inj j.1)) := by
  classical
  exact Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc hc fun i =>
      if h : p i then s.inj ⟨i, h⟩ else (hz i h).to_ s.pt)
    (fun s j => by
      change c.inj j.1 ≫ _ = _
      rw [Cofan.IsColimit.fac, dif_pos j.2])
    (fun s m hm => Cofan.IsColimit.hom_ext hc _ _ fun i => by
      rw [Cofan.IsColimit.fac]
      split_ifs with h
      · exact hm ⟨i, h⟩
      · exact (hz i h).eq_of_src _ _)

/-- A skyscraper sheaf with zero value is zero. -/
theorem isZero_pointSheaf {T : TopCat.{u}} (P : T) (B : AddCommGrpCat.{u})
    (hB : ∀ b : B, b = 0) : IsZero (pointSheaf P B) := by
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  ext U s
  exact LocallyConstant.ext fun x => (hB _).trans (hB _).symm

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X]

/-- The cofan of the skyscrapers `i_{P,*}(Ω_{K/k}/Ω_{X,P})` over the closed points `P`. -/
def differentialPrincipalPartsClosedCofan :
    Cofan (fun P : {P : X // IsClosed ({P} : Set X)} =>
      pointSheaf (X := X.toTopCat) P.1 (differentialPrincipalPartsGroup k X P.1)) :=
  Cofan.mk (differentialPrincipalPartsSheaf k X)
    (fun P => pointToLocallyFiniteSum (X := X.toTopCat) (differentialPrincipalPartsGroup k X) P.1)

variable {k X}

/-- **The sheaf of differential principal parts is the direct sum
`⨁_{P closed} i_{P,*}(Ω_{K/k}/Ω_{X,P})`**: the coproduct of the skyscrapers over the closed
points, with the summand inclusions as coprojections. The only other point is the generic point,
where `Ω_{X,η} = Ω_{K/k}`. -/
def isColimitDifferentialPrincipalPartsClosedCofan (hX : X.IsNonsingularCurve k) :
    IsColimit (differentialPrincipalPartsClosedCofan k X) :=
  have : IsNoetherian X := hX.satisfiesConditionStar.isNoetherian
  have : NoetherianSpace X.toTopCat := inferInstanceAs (NoetherianSpace X)
  isColimitCofanSubtypeOfIsZero
    (isColimitLocallyFiniteSumCofan (X := X.toTopCat) (A := differentialPrincipalPartsGroup k X))
    (fun P => IsClosed ({P} : Set X)) fun P hP => by
    have hPη : P = genericPoint X := by
      by_contra h
      exact hP (isClosed_singleton_of_ne_genericPoint hX h)
    subst hPη
    exact isZero_pointSheaf _ _ differentialPrincipalPartsGroup_genericPoint_eq_zero

end ClosedPoints

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X]

/-- **The differential principal-parts resolution** (Hartshorne III.7, p. 248). Let `X` be a
nonsingular curve over an algebraically closed field `k`, with function field `K`, `Ω_X = Ω_{X/k}`
and `Ω_K` the constant sheaf with value `Ω_{K/k}`. Then:

* for every point `P`, the stalk `Ω_{X,P}` embeds into `Ω_{K/k}`, with image the subgroup used to
  form the principal parts `Ω_{K/k}/Ω_{X,P}`;
* `0 → Ω_X → Ω_K → ⨁_P i_{P,*}(Ω_{K/k}/Ω_{X,P}) → 0` is a short exact sequence of sheaves of
  abelian groups;
* its last two terms are flasque;
* the third term is the direct sum of the skyscrapers `i_{P,*}(Ω_{K/k}/Ω_{X,P})` over the closed
  points `P`, with the summand inclusions as coprojections;
* consequently `H¹(X, Ω_X)` is the cokernel of the principal-parts map on global sections.

Hartshorne states this for a complete curve; completeness is not used. -/
theorem curveDifferential_principalPartsResolution (hX : X.IsNonsingularCurve k) :
    (∀ P : X, Function.Injective (differentialsStalkToGeneric (X ↘ Spec (.of k)) P) ∧
      (differentialsStalkToGeneric (X ↘ Spec (.of k)) P).hom.range =
        differentialsStalkRange (X ↘ Spec (.of k)) P) ∧
    (differentialPrincipalPartsComplex hX).ShortExact ∧
    (differentialPrincipalPartsComplex hX).X₂.IsFlasque ∧
    (differentialPrincipalPartsComplex hX).X₃.IsFlasque ∧
    Nonempty (IsColimit (differentialPrincipalPartsClosedCofan k X)) ∧
    Nonempty ((sheafCohomology X.toTopCat 1).obj (differentialPrincipalPartsComplex hX).X₁ ≅
      cokernel ((differentialPrincipalPartsComplex hX).g.hom.app (op ⊤))) := by
  have := functionFieldDifferentials_nontrivial hX
  exact ⟨fun P => ⟨differentialsStalkToGeneric_injective _
      (relativeDifferentials_isLocallyFreeOfRank_one hX) P,
      range_differentialsStalkToGeneric _ P⟩,
    differentialPrincipalPartsComplex_shortExact hX, isFlasque_rationalDifferentialsSheaf,
    isFlasque_differentialPrincipalPartsSheaf hX,
    ⟨isColimitDifferentialPrincipalPartsClosedCofan hX⟩,
    sheafCohomology_one_curveDifferentials_iso_cokernel hX⟩

end Main

end Hartshorne
