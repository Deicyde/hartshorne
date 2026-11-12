/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Hartshorne.Cohomology.ReductionAffineIff
import Hartshorne.Scheme.ClosedImmersionIdealSheaf
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Hartshorne.Scheme.Differentials.AffineNonsingularInfinitesimalLifting

/-!
# Infinitesimal extensions of a nonsingular affine scheme

Hartshorne, *Algebraic Geometry*, II, Exercise 8.7 (pp. 189–190).

Let `X` be a scheme over `k` and `F` an `𝒪_X`-module. An *infinitesimal extension* of `X` by `F`
(`Hartshorne.InfinitesimalExtension`) is a `k`-scheme `X'` with a sheaf of ideals `I` such that
`I² = 0`, `(X', 𝒪_{X'}/I) ≅ X` over `k`, and `I ≅ F` as `𝒪_X`-modules. The *trivial extension*
is the topological space of `X` with the sheaf of rings `𝒪_X ⊕ F`, where
`(a ⊕ f)(a' ⊕ f') = a a' ⊕ (a f' + a' f)`
(`Hartshorne.InfinitesimalExtension.trivialExtensionPresheaf`). An isomorphism of an extension
with the trivial one is recorded by `Hartshorne.InfinitesimalExtension.TrivialIso`.

The main result (`Hartshorne.InfinitesimalExtension.nonempty_trivialIso`): if `k` is
algebraically closed, `X` is affine, nonsingular and of finite type over `k`, and `F` is
coherent, then every infinitesimal extension of `X` by `F` is isomorphic to the trivial one.

## Proof

* The ideal `I` is nil, so the closed immersion `ι : X ⟶ X'` is surjective, hence a homeomorphism
  (`Hartshorne.InfinitesimalExtension.isHomeomorph`).
* On an affine open `U ⊆ X'`, `Γ(U, 𝒪_{X'})` is an extension of the Noetherian ring
  `Γ(ι⁻¹ U, 𝒪_X)` by the finitely generated module `Γ(ι⁻¹ U, F)`, so it is Noetherian; thus `X'`
  is Noetherian. Its reduction is a closed subscheme of the affine scheme `X`, so `X'` is affine
  by Hartshorne III, Exercise 3.1 (`Hartshorne.InfinitesimalExtension.isAffine_scheme`).
* Hence `Γ(X', 𝒪_{X'}) → Γ(X, 𝒪_X)` is a surjection of `k`-algebras with square-zero kernel, and
  the infinitesimal lifting property (Hartshorne II, Exercise 8.6) lifts the identity of
  `Γ(X, 𝒪_X)` to a section. As `X` is affine this is a retraction `ρ : X' ⟶ X` of `ι` over `k`
  (`Hartshorne.InfinitesimalExtension.exists_retraction`).
* On every open `U ⊆ X'`, `(a, m) ↦ ρ^# a + m` is a ring isomorphism
  `Γ(ι⁻¹ U, 𝒪_X) ⊕ Γ(ι⁻¹ U, F) → Γ(U, 𝒪_{X'})`: it is a section of `ι^#` plus the inclusion of
  the kernel `I ≅ F` of `ι^#` (`Hartshorne.InfinitesimalExtension.splitHom_bijective`). These
  maps form an isomorphism of presheaves of rings `ι_* (𝒪_X ⊕ F) ≅ 𝒪_{X'}`
  (`Hartshorne.InfinitesimalExtension.split`).
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

namespace InfinitesimalExtension

/-! ### Trivial square-zero extensions of a commutative ring -/

section Ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A commutative ring `R` acts on the right of an `R`-module `M` by its left action. -/
abbrev opModule : Module Rᵐᵒᵖ M := Module.compHom M (RingEquiv.toOpposite R).symm.toRingHom

attribute [local instance] opModule

/-- The two actions of `R` on `M` given by `opModule` agree. -/
theorem opModule_isCentralScalar : IsCentralScalar R M := ⟨fun _ _ => rfl⟩

attribute [local instance] opModule_isCentralScalar

/-- The ring homomorphism `R ⊕ M → S ⊕ N`, `(r, m) ↦ (φ r, ψ m)`, of trivial square-zero
extensions along a ring homomorphism `φ` and a `φ`-semilinear map `ψ`. -/
def mapHom {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N] (φ : R →+* S) (ψ : M →+ N)
    (hψ : ∀ (r : R) (m : M), ψ (r • m) = φ r • ψ m) :
    TrivSqZeroExt R M →+* TrivSqZeroExt S N where
  toFun x := ⟨φ x.fst, ψ x.snd⟩
  map_one' := TrivSqZeroExt.ext (map_one φ) (map_zero ψ)
  map_mul' x y := TrivSqZeroExt.ext (map_mul φ _ _) (by
    change ψ (x.fst • y.snd + y.fst • x.snd) = φ x.fst • ψ y.snd + φ y.fst • ψ x.snd
    rw [map_add, hψ, hψ])
  map_zero' := TrivSqZeroExt.ext (map_zero φ) (map_zero ψ)
  map_add' x y := TrivSqZeroExt.ext (map_add φ _ _) (map_add ψ _ _)

/-- The ring homomorphism `R ⊕ M → A`, `(r, m) ↦ f r + g m`, out of a trivial square-zero
extension, for a ring homomorphism `f` and an additive map `g` with `g m * g m' = 0` and
`g (r • m) = f r * g m`. -/
def liftHom {A : Type*} [CommRing A] (f : R →+* A) (g : M →+ A) (hg : ∀ m m', g m * g m' = 0)
    (hfg : ∀ (r : R) (m : M), g (r • m) = f r * g m) : TrivSqZeroExt R M →+* A where
  toFun x := f x.fst + g x.snd
  map_one' := by simp
  map_mul' x y := by
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, map_mul, map_add]
    change _ + (g (x.fst • y.snd) + g (y.fst • x.snd)) = _
    rw [hfg, hfg]
    linear_combination -hg x.snd y.snd
  map_zero' := by simp
  map_add' x y := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]; ring

theorem liftHom_apply {A : Type*} [CommRing A] (f : R →+* A) (g : M →+ A)
    (hg : ∀ m m', g m * g m' = 0) (hfg : ∀ (r : R) (m : M), g (r • m) = f r * g m)
    (x : TrivSqZeroExt R M) : liftHom f g hg hfg x = f x.fst + g x.snd := rfl

end Ring

attribute [local instance] opModule opModule_isCentralScalar

/-! ### The trivial extension of a scheme by a module -/

variable {X : Scheme.{u}}

/-- The structure presheaf of the **trivial extension** of `X` by an `𝒪_X`-module `F`
(Hartshorne II, Exercise 8.7): the presheaf of rings `𝒪_X ⊕ F` on the topological space of `X`,
with `Γ(U, 𝒪_X ⊕ F) = Γ(U, 𝒪_X) ⊕ Γ(U, F)` and multiplication
`(a ⊕ f) · (a' ⊕ f') = a a' ⊕ (a f' + a' f)`. -/
def trivialExtensionPresheaf (F : X.Modules) : TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of (TrivSqZeroExt Γ(X, U.unop) Γ(F, U.unop))
  map {U V} h := CommRingCat.ofHom
    (mapHom (X.presheaf.map h).hom (F.presheaf.map h).hom fun r m => F.map_smul h.unop r m)
  map_id U := by
    ext x
    · exact congr($(X.presheaf.map_id U) x.fst)
    · exact congr($(F.presheaf.map_id U) x.snd)
  map_comp {U V W} h h' := by
    ext x
    · exact congr($(X.presheaf.map_comp h h') x.fst)
    · exact congr($(F.presheaf.map_comp h h') x.snd)

/-- The projection `𝒪_X ⊕ F → 𝒪_X` of the trivial extension onto `𝒪_X`. -/
def trivialExtensionFst (F : X.Modules) : trivialExtensionPresheaf F ⟶ X.presheaf where
  app U := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℤ Γ(X, U.unop) Γ(F, U.unop)).toRingHom
  naturality _ _ _ := rfl

end InfinitesimalExtension

open InfinitesimalExtension

/-- An **infinitesimal extension** of a `k`-scheme `X` by an `𝒪_X`-module `F` (Hartshorne II,
Exercise 8.7): a `k`-scheme `X'` with a sheaf of ideals `I` such that `I² = 0`,
`(X', 𝒪_{X'}/I) ≅ X` over `k`, and `I ≅ F` as `𝒪_X`-modules.

The isomorphism `(X', 𝒪_{X'}/I) ≅ X` is recorded as a closed immersion `ι : X ⟶ X'` over `k`
with ideal sheaf `I = ker (𝒪_{X'} → ι_* 𝒪_X)`. Since `I² = 0`, `I` is a module over
`𝒪_{X'}/I = ι_* 𝒪_X`, and an isomorphism `I ≅ F` of `𝒪_X`-modules is the same as an
isomorphism `ι_* F ≅ I` of `𝒪_{X'}`-modules. -/
structure InfinitesimalExtension {k : Type u} [CommRing k] {X : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (F : X.Modules) where
  /-- The scheme `X'`. -/
  scheme : Scheme.{u}
  /-- The structure morphism of `X'` over `k`. -/
  over : scheme ⟶ Spec (.of k)
  /-- The closed immersion `X ⟶ X'` identifying `X` with `(X', 𝒪_{X'}/I)`. -/
  ι : X ⟶ scheme
  [isClosedImmersion : IsClosedImmersion ι]
  ι_over : ι ≫ over = pX
  /-- The ideal sheaf `I` of `ι` has square zero. -/
  sq_eq_zero : ∀ (U : scheme.Opens) (a b : Γ(closedImmersionIdealSheaf ι, U)),
    (show Γ(scheme, U) from (closedImmersionIdealSheafι ι).app U a) *
      (show Γ(scheme, U) from (closedImmersionIdealSheafι ι).app U b) = 0
  /-- The isomorphism `I ≅ F` of `𝒪_X`-modules. -/
  iso : (Scheme.Modules.pushforward ι).obj F ≅ closedImmersionIdealSheaf ι

namespace InfinitesimalExtension

attribute [local instance] opModule opModule_isCentralScalar

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {pX : X ⟶ Spec (.of k)} {F : X.Modules}

/-- An **isomorphism of an infinitesimal extension `(X', I)` of `X` by `F` with the trivial
extension** `(X, 𝒪_X ⊕ F)` (Hartshorne II, Exercise 8.7): an isomorphism of sheaves of rings
`𝒪_{X'} ≅ ι_* (𝒪_X ⊕ F)` along `ι` (an isomorphism of ringed spaces
`(X', 𝒪_{X'}) ≅ (X, 𝒪_X ⊕ F)` when `ι` is a homeomorphism), which
* is compatible with the identifications of `X` with `(X', 𝒪_{X'}/I)` and with
  `(X, (𝒪_X ⊕ F)/F)`, i.e. with `ι^# : 𝒪_{X'} → ι_* 𝒪_X` and the projection `𝒪_X ⊕ F → 𝒪_X`;
* is compatible with the structures over `k`;
* restricts to the given isomorphism `I ≅ F` on the ideals. -/
structure TrivialIso (E : InfinitesimalExtension pX F) where
  /-- The isomorphism of sheaves of rings `𝒪_{X'} ≅ ι_* (𝒪_X ⊕ F)`. -/
  iso : E.scheme.presheaf ≅ E.ι.base _* trivialExtensionPresheaf F
  comp_fst : iso.hom ≫ (TopCat.Presheaf.pushforward _ E.ι.base).map (trivialExtensionFst F) =
    E.ι.c
  app_over (c : Γ(Spec (.of k), ⊤)) :
    iso.hom.app (op ⊤) (E.over.appTop c) = TrivSqZeroExt.inl (pX.appTop c)
  app_ideal (U : E.scheme.Opens) (m : Γ(F, E.ι ⁻¹ᵁ U)) :
    iso.hom.app (op U) (show Γ(E.scheme, U) from Scheme.Modules.Hom.app
      (closedImmersionIdealSheafι E.ι) U (E.iso.hom.app U m)) = TrivSqZeroExt.inr m

end InfinitesimalExtension

namespace InfinitesimalExtension

/-! ### Sections of the ideal sheaf of a closed immersion -/

section KernelSections

variable {Y Z : Scheme.{u}} (i : Y ⟶ Z) (U : Z.Opens)

/-- Sections over `U` of `𝒪_Z`-modules, as a functor to abelian groups. -/
abbrev sectionsFunctor : SheafOfModules.{u} Z.ringCatSheaf ⥤ Ab.{u} :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙ (evaluation _ _).obj (op U)

instance : PreservesLimits (sectionsFunctor U) :=
  have : PreservesLimits ((evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).obj (op U)) :=
    evaluationPreservesLimits _
  have : PreservesLimits (PresheafOfModules.toPresheaf.{u} Z.ringCatSheaf.obj ⋙
      (evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).obj (op U)) := comp_preservesLimits _ _
  comp_preservesLimits _ _

instance : (sectionsFunctor U).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩

theorem structureSheafToPushforward_app_apply (x : Γ(Z, U)) :
    Scheme.Modules.Hom.app (structureSheafToPushforward i) U x = i.app U x := rfl

/-- The inclusion `Γ(U, I) → Γ(U, 𝒪_Z)` of sections of the ideal sheaf of `i` is injective. -/
theorem closedImmersionIdealSheafι_app_injective :
    Function.Injective (Scheme.Modules.Hom.app (closedImmersionIdealSheafι i) U) :=
  (AddCommGrpCat.mono_iff_injective _).mp
    (have : Mono (kernel.ι (structureSheafToPushforward i)) := equalizer.ι_mono
    (sectionsFunctor U).map_mono (kernel.ι (structureSheafToPushforward i)))

theorem app_closedImmersionIdealSheafι_app (a : Γ(closedImmersionIdealSheaf i, U)) :
    i.app U (Scheme.Modules.Hom.app (closedImmersionIdealSheafι i) U a) = 0 := by
  have h := kernel.condition (structureSheafToPushforward i)
  exact congr(($h).val.app (op U) a)

/-- A section of `𝒪_Z` killed by `i^#` is a section of the ideal sheaf of `i`. -/
theorem exists_closedImmersionIdealSheafι_app (x : Γ(Z, U)) (hx : i.app U x = 0) :
    ∃ a, Scheme.Modules.Hom.app (closedImmersionIdealSheafι i) U a = x := by
  let S := ShortComplex.mk (C := SheafOfModules.{u} Z.ringCatSheaf)
    (kernel.ι (structureSheafToPushforward i)) (structureSheafToPushforward i)
    (kernel.condition _)
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel _)
  have h := hS.map_of_mono_of_preservesKernel (sectionsFunctor U) equalizer.ι_mono
    inferInstance
  exact (ShortComplex.ab_exact_iff _).mp h x hx

end KernelSections

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {pX : X ⟶ Spec (.of k)} {F : X.Modules}
  (E : InfinitesimalExtension pX F)

attribute [local instance] InfinitesimalExtension.isClosedImmersion opModule
  opModule_isCentralScalar

/-- The ideal sheaf of an infinitesimal extension lies in the nilradical. -/
theorem ker_le_nilradical : E.ι.ker ≤ E.scheme.nilradical := by
  intro U x hx
  rw [Scheme.Hom.ker_apply] at hx
  obtain ⟨a, rfl⟩ := exists_closedImmersionIdealSheafι_app E.ι U x hx
  exact ⟨2, (pow_two (M := Γ(E.scheme, U)) _).trans (E.sq_eq_zero U a a)⟩

/-- The closed immersion `X ⟶ X'` of an infinitesimal extension is surjective. -/
theorem surjective : Function.Surjective E.ι.base := by
  have h := Scheme.IdealSheafData.support_antitone E.ker_le_nilradical
  intro x
  have hx : x ∈ (E.ι.ker.support : Set E.scheme) :=
    h (by rw [Scheme.support_nilradical]; trivial)
  rw [Scheme.Hom.support_ker, E.ι.isClosedEmbedding.isClosed_range.closure_eq] at hx
  exact hx

/-- The closed immersion `X ⟶ X'` of an infinitesimal extension is a homeomorphism. -/
theorem isHomeomorph : IsHomeomorph E.ι.base :=
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨E.ι.isClosedEmbedding.isEmbedding, E.surjective⟩

/-! ### `X'` is Noetherian and affine -/

/-- Restriction of scalars along a surjective ring homomorphism preserves Noetherian modules. -/
theorem isNoetherian_of_surjective_algebraMap {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) [IsNoetherian S M] : IsNoetherian R M := by
  refine ⟨fun N => ?_⟩
  let N' : Submodule S M :=
    { N with
      smul_mem' := fun s m hm => by
        obtain ⟨r, rfl⟩ := h s
        rw [algebraMap_smul]
        exact N.smul_mem r hm }
  exact (IsNoetherian.noetherian N').restrictScalars_of_surjective h

/-- If `X` is locally Noetherian and `F` is coherent, then the sections of `𝒪_{X'}` over every
affine open form a Noetherian ring: they are an extension of the Noetherian ring `Γ(ι⁻¹ U, 𝒪_X)`
by the finitely generated module `Γ(ι⁻¹ U, F)`. -/
theorem isNoetherianRing_sections [IsLocallyNoetherian X] (hF : IsCoherent F)
    (U : E.scheme.affineOpens) : IsNoetherianRing Γ(E.scheme, U) := by
  have hV : IsAffineOpen (E.ι ⁻¹ᵁ (U : E.scheme.Opens)) := U.2.preimage E.ι
  have : IsNoetherianRing Γ(X, E.ι ⁻¹ᵁ (U : E.scheme.Opens)) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hV⟩
  have h4 := (coherent_affine_local_tfae F).out 0 3
  have hfin := (h4.mp hF ⟨_, hV⟩).1
  let : Algebra Γ(E.scheme, U) Γ(X, E.ι ⁻¹ᵁ (U : E.scheme.Opens)) := (E.ι.app U).hom.toAlgebra
  have hsurj : Function.Surjective
      (algebraMap Γ(E.scheme, U) Γ(X, E.ι ⁻¹ᵁ (U : E.scheme.Opens))) :=
    E.ι.app_surjective U U.2
  let : Module Γ(X, E.ι ⁻¹ᵁ (U : E.scheme.Opens))
      Γ((Scheme.Modules.pushforward E.ι).obj F, (U : E.scheme.Opens)) :=
    inferInstanceAs (Module Γ(X, E.ι ⁻¹ᵁ (U : E.scheme.Opens)) Γ(F, E.ι ⁻¹ᵁ (U : E.scheme.Opens)))
  have : IsScalarTower Γ(E.scheme, U) Γ(X, E.ι ⁻¹ᵁ (U : E.scheme.Opens))
      Γ((Scheme.Modules.pushforward E.ι).obj F, (U : E.scheme.Opens)) :=
    ⟨fun r s m => mul_smul (E.ι.app U r) s m⟩
  have : Module.Finite Γ(X, E.ι ⁻¹ᵁ (U : E.scheme.Opens))
      Γ((Scheme.Modules.pushforward E.ι).obj F, (U : E.scheme.Opens)) := hfin
  have : IsNoetherian Γ(E.scheme, U)
      Γ((Scheme.Modules.pushforward E.ι).obj F, (U : E.scheme.Opens)) :=
    isNoetherian_of_surjective_algebraMap hsurj
  have : IsNoetherian Γ(E.scheme, U) Γ(X, E.ι ⁻¹ᵁ (U : E.scheme.Opens)) :=
    isNoetherian_of_surjective_algebraMap hsurj
  let f : Γ((Scheme.Modules.pushforward E.ι).obj F, (U : E.scheme.Opens)) →ₗ[Γ(E.scheme, U)]
      Γ(E.scheme, U) :=
    { toFun := fun m => Scheme.Modules.Hom.app (closedImmersionIdealSheafι E.ι) U
        (E.iso.hom.app U m)
      map_add' := fun _ _ => by rw [map_add, map_add]; rfl
      map_smul' := fun r m => by
        rw [Scheme.Modules.Hom.app_smul]
        exact ((closedImmersionIdealSheafι E.ι).val.app (op (U : E.scheme.Opens))).hom.map_smul
          r _ }
  refine isNoetherian_of_range_eq_ker f
    (Algebra.linearMap Γ(E.scheme, U) Γ(X, E.ι ⁻¹ᵁ (U : E.scheme.Opens))) ?_
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Algebra.linearMap_apply]
  constructor
  · rintro ⟨m, rfl⟩
    exact app_closedImmersionIdealSheafι_app E.ι U _
  · intro hx
    obtain ⟨a, rfl⟩ := exists_closedImmersionIdealSheafι_app E.ι U x hx
    refine ⟨E.iso.inv.app U a, ?_⟩
    change Scheme.Modules.Hom.app (closedImmersionIdealSheafι E.ι) U
      ((E.iso.inv ≫ E.iso.hom).app U a) = _
    rw [E.iso.inv_hom_id]
    rfl

/-- If `X` is affine and Noetherian and `F` is coherent, then `X'` is Noetherian. -/
theorem isNoetherian_scheme [IsAffine X] [IsLocallyNoetherian X] (hF : IsCoherent F) :
    IsNoetherian E.scheme :=
  have : IsLocallyNoetherian E.scheme := ⟨E.isNoetherianRing_sections hF⟩
  have : CompactSpace E.scheme := E.surjective.compactSpace E.ι.continuous
  ⟨⟩

/-- If `X` is affine and Noetherian and `F` is coherent, then `X'` is affine: its reduction is a
closed subscheme of `X`, and a Noetherian scheme with affine reduction is affine (Hartshorne III,
Exercise 3.1). -/
theorem isAffine_scheme [IsAffine X] [IsLocallyNoetherian X] (hF : IsCoherent F) :
    IsAffine E.scheme := by
  have := E.isNoetherian_scheme hF
  rw [ReductionAffine.isAffine_iff_isAffine_reduced]
  have H : E.ι.ker ≤ E.scheme.nilradical.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact E.ker_le_nilradical
  let j := IsClosedImmersion.lift E.ι E.scheme.nilradical.subschemeι H
  have : IsClosedImmersion (j ≫ E.ι) := by
    rw [IsClosedImmersion.lift_fac]
    infer_instance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp_isClosedImmersion j E.ι
  exact isAffine_of_isAffineHom j

/-! ### The ideal sheaf as a subsheaf of `𝒪_{X'}` -/

/-- The composite `Γ(ι⁻¹ U, F) ≅ Γ(U, I) ⊆ Γ(U, 𝒪_{X'})`. -/
def idealIncl (U : E.scheme.Opens) : Γ(F, E.ι ⁻¹ᵁ U) →+ Γ(E.scheme, U) :=
  ((closedImmersionIdealSheafι E.ι).val.app (op U)).hom.toAddMonoidHom.comp
    (E.iso.hom.app U).hom

theorem idealIncl_mul (U : E.scheme.Opens) (m m' : Γ(F, E.ι ⁻¹ᵁ U)) :
    E.idealIncl U m * E.idealIncl U m' = 0 :=
  E.sq_eq_zero U _ _

theorem idealIncl_smul (U : E.scheme.Opens) (b : Γ(E.scheme, U)) (m : Γ(F, E.ι ⁻¹ᵁ U)) :
    E.idealIncl U (E.ι.app U b • m) = b * E.idealIncl U m := by
  change Scheme.Modules.Hom.app (closedImmersionIdealSheafι E.ι) U (E.iso.hom.app U
    (b • (show Γ((Scheme.Modules.pushforward E.ι).obj F, U) from m))) = _
  rw [Scheme.Modules.Hom.app_smul]
  exact ((closedImmersionIdealSheafι E.ι).val.app (op U)).hom.map_smul b _

theorem app_idealIncl (U : E.scheme.Opens) (m : Γ(F, E.ι ⁻¹ᵁ U)) :
    E.ι.app U (E.idealIncl U m) = 0 :=
  app_closedImmersionIdealSheafι_app E.ι U _

theorem idealIncl_injective (U : E.scheme.Opens) : Function.Injective (E.idealIncl U) := by
  intro m m' h
  have h' := closedImmersionIdealSheafι_app_injective E.ι U h
  have := congr(E.iso.inv.app U $h')
  change (E.iso.hom ≫ E.iso.inv).app U m = (E.iso.hom ≫ E.iso.inv).app U m' at this
  rwa [E.iso.hom_inv_id] at this

theorem exists_idealIncl (U : E.scheme.Opens) (x : Γ(E.scheme, U)) (hx : E.ι.app U x = 0) :
    ∃ m, E.idealIncl U m = x := by
  obtain ⟨a, rfl⟩ := exists_closedImmersionIdealSheafι_app E.ι U x hx
  refine ⟨E.iso.inv.app U a, ?_⟩
  change Scheme.Modules.Hom.app (closedImmersionIdealSheafι E.ι) U
    ((E.iso.inv ≫ E.iso.hom).app U a) = _
  rw [E.iso.inv_hom_id]
  rfl

theorem idealIncl_naturality {U V : E.scheme.Opensᵒᵖ} (h : U ⟶ V) (m : Γ(F, E.ι ⁻¹ᵁ U.unop)) :
    E.scheme.presheaf.map h (E.idealIncl U.unop m) =
      E.idealIncl V.unop (F.presheaf.map ((Opens.map E.ι.base).map h.unop).op m) := by
  have h1 : E.iso.hom.app V.unop (((Scheme.Modules.pushforward E.ι).obj F).presheaf.map h m) =
      (closedImmersionIdealSheaf E.ι).presheaf.map h (E.iso.hom.app U.unop m) :=
    ConcreteCategory.congr_hom (E.iso.hom.mapPresheaf.naturality h) m
  have h2 : Scheme.Modules.Hom.app (closedImmersionIdealSheafι E.ι) V.unop
      ((closedImmersionIdealSheaf E.ι).presheaf.map h (E.iso.hom.app U.unop m)) =
      E.scheme.presheaf.map h (E.idealIncl U.unop m) :=
    ConcreteCategory.congr_hom
      ((Scheme.Modules.Hom.mapPresheaf (closedImmersionIdealSheafι E.ι)).naturality h)
      (E.iso.hom.app U.unop m)
  change _ = Scheme.Modules.Hom.app (closedImmersionIdealSheafι E.ι) V.unop
    (E.iso.hom.app V.unop (((Scheme.Modules.pushforward E.ι).obj F).presheaf.map h m))
  rw [h1, h2]

/-! ### Splitting `𝒪_{X'}` along a retraction `X' ⟶ X` -/

section Retraction

variable (ρ : E.scheme ⟶ X) (hρ : E.ι ≫ ρ = 𝟙 X)

include hρ in
theorem ι_ρ_apply (x : E.scheme) : E.ι.base (ρ.base x) = x := by
  obtain ⟨y, rfl⟩ := E.surjective x
  have : ρ.base (E.ι.base y) = y := by
    rw [← Scheme.Hom.comp_apply, hρ]
    rfl
  rw [this]

include hρ in
theorem le_preimage (U : E.scheme.Opens) : U ≤ ρ ⁻¹ᵁ (E.ι ⁻¹ᵁ U) := fun x hx => by
  change E.ι.base (ρ.base x) ∈ U
  rwa [E.ι_ρ_apply ρ hρ]

include hρ in
theorem app_appLE (U : E.scheme.Opens) (a : Γ(X, E.ι ⁻¹ᵁ U)) :
    E.ι.app U (ρ.appLE (E.ι ⁻¹ᵁ U) U (E.le_preimage ρ hρ U) a) = a := by
  have key : ∀ φ : X ⟶ X, φ = 𝟙 X → ∀ (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ V),
      φ.appLE V V e = 𝟙 _ := by
    rintro _ rfl V e
    simp only [Scheme.Hom.appLE]
    exact (Category.id_comp _).trans (X.presheaf.map_id (op V))
  rw [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE,
    key _ hρ]
  rfl

/-- The ring homomorphism `Γ(ι⁻¹ U, 𝒪_X) ⊕ Γ(ι⁻¹ U, F) → Γ(U, 𝒪_{X'})`, `(a, m) ↦ ρ^# a + m`,
given by a retraction `ρ` of `ι` and the inclusion `F ≅ I ⊆ 𝒪_{X'}`. -/
def splitHom (U : E.scheme.Opens) :
    TrivSqZeroExt Γ(X, E.ι ⁻¹ᵁ U) Γ(F, E.ι ⁻¹ᵁ U) →+* Γ(E.scheme, U) :=
  liftHom (ρ.appLE (E.ι ⁻¹ᵁ U) U (E.le_preimage ρ hρ U)).hom (E.idealIncl U) (E.idealIncl_mul U)
    (fun r m => by
      conv_lhs => rw [← E.app_appLE ρ hρ U r]
      exact E.idealIncl_smul U _ m)

theorem app_splitHom (U : E.scheme.Opens) (x : TrivSqZeroExt Γ(X, E.ι ⁻¹ᵁ U) Γ(F, E.ι ⁻¹ᵁ U)) :
    E.ι.app U (E.splitHom ρ hρ U x) = x.fst := by
  rw [splitHom, liftHom_apply, map_add, E.app_idealIncl, add_zero]
  exact E.app_appLE ρ hρ U x.fst

theorem splitHom_bijective (U : E.scheme.Opens) : Function.Bijective (E.splitHom ρ hρ U) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun y => ?_⟩
  · have h1 : x.fst = 0 := by rw [← E.app_splitHom ρ hρ U x, hx, map_zero]
    rw [splitHom, liftHom_apply, h1, map_zero, zero_add] at hx
    exact TrivSqZeroExt.ext h1 (E.idealIncl_injective U (hx.trans (map_zero _).symm))
  · obtain ⟨m, hm⟩ := E.exists_idealIncl U
      (y - ρ.appLE (E.ι ⁻¹ᵁ U) U (E.le_preimage ρ hρ U) (E.ι.app U y))
      (by rw [map_sub, E.app_appLE ρ hρ, sub_self])
    refine ⟨show TrivSqZeroExt _ _ from (E.ι.app U y, m), ?_⟩
    change ρ.appLE (E.ι ⁻¹ᵁ U) U (E.le_preimage ρ hρ U) (E.ι.app U y) + E.idealIncl U m = y
    rw [hm, add_sub_cancel]

/-- The morphism of presheaves of rings `ι_* (𝒪_X ⊕ F) ⟶ 𝒪_{X'}` given by a retraction `ρ`. -/
def split : E.ι.base _* trivialExtensionPresheaf F ⟶ E.scheme.presheaf where
  app U := CommRingCat.ofHom (E.splitHom ρ hρ U.unop)
  naturality U V h := by
    ext x
    change ρ.appLE (E.ι ⁻¹ᵁ V.unop) V.unop (E.le_preimage ρ hρ V.unop)
        (X.presheaf.map ((Opens.map E.ι.base).map h.unop).op x.fst) +
        E.idealIncl V.unop (F.presheaf.map ((Opens.map E.ι.base).map h.unop).op x.snd) =
      E.scheme.presheaf.map h (ρ.appLE (E.ι ⁻¹ᵁ U.unop) U.unop (E.le_preimage ρ hρ U.unop) x.fst +
        E.idealIncl U.unop x.snd)
    rw [map_add, E.idealIncl_naturality]
    congr 1
    change (X.presheaf.map _ ≫ ρ.appLE _ _ _) x.fst = (ρ.appLE _ _ _ ≫ E.scheme.presheaf.map h)
      x.fst
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
    rfl

instance isIso_split : IsIso (E.split ρ hρ) := by
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun U => ?_
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (E.splitHom_bijective ρ hρ U.unop)

end Retraction

/-! ### A retraction from the infinitesimal lifting property -/

/-- Regularity is invariant under isomorphism. -/
theorem isRegular_of_iso {Y Z : Scheme.{u}} (e : Y ≅ Z) (hZ : Z.IsRegular) : Y.IsRegular := by
  have := hZ.1
  refine ⟨isLocallyNoetherian_of_isOpenImmersion e.hom, fun y => ?_⟩
  have : IsRegularLocalRing (Z.presheaf.stalk (e.hom.base y)) := hZ.2 _
  exact IsRegularLocalRing.of_ringEquiv (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv

end InfinitesimalExtension

namespace InfinitesimalExtension

attribute [local instance] InfinitesimalExtension.isClosedImmersion opModule
  opModule_isCentralScalar

variable {k : Type u} [Field k] {X : Scheme.{u}} {pX : X ⟶ Spec (.of k)} {F : X.Modules}
  (E : InfinitesimalExtension pX F)

/-- If `k` is algebraically closed, `X` is affine, nonsingular and of finite type over `k`, and
`F` is coherent, then the closed immersion `ι : X ⟶ X'` has a retraction over `k`: `X'` is
affine, and by the infinitesimal lifting property (Hartshorne II, Exercise 8.6) the identity of
`Γ(X, 𝒪_X)` lifts along the surjection `Γ(X', 𝒪_{X'}) → Γ(X, 𝒪_X)`, whose kernel has square
zero. -/
theorem exists_retraction [IsAlgClosed k] [LocallyOfFiniteType pX] [IsAffine X]
    (hX : X.IsRegular) (hF : IsCoherent F) :
    ∃ ρ : E.scheme ⟶ X, E.ι ≫ ρ = 𝟙 X ∧ ρ ≫ pX = E.over := by
  have := hX.1
  have := E.isAffine_scheme hF
  let φk : k →+* Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k Γ(X, ⊤) := (pX.appTop.hom.comp φk).toAlgebra
  let : Algebra k Γ(E.scheme, ⊤) := (E.over.appTop.hom.comp φk).toAlgebra
  have : Algebra.FiniteType k Γ(X, ⊤) := by
    have h1 : pX.appTop.hom.FiniteType := HasRingHomProperty.appTop @LocallyOfFiniteType pX ‹_›
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  have hcomm : ∀ c, E.ι.appTop (E.over.appTop c) = pX.appTop c := fun c =>
    congrArg (fun φ : X ⟶ Spec (.of k) => φ.appTop c) E.ι_over
  let g : Γ(E.scheme, ⊤) →ₐ[k] Γ(X, ⊤) :=
    { E.ι.appTop.hom with commutes' := fun c => hcomm (φk c) }
  have hg : Function.Surjective g := (IsClosedImmersion.isAffine_surjective_of_isAffine E.ι).2
  have hI : RingHom.ker g ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := exists_closedImmersionIdealSheafι_app E.ι ⊤ x hx
    obtain ⟨b, rfl⟩ := exists_closedImmersionIdealSheafι_app E.ι ⊤ y hy
    exact Ideal.mem_bot.mpr (E.sq_eq_zero ⊤ a b)
  have hreg : (Spec (CommRingCat.of Γ(X, ⊤))).IsRegular := isRegular_of_iso X.isoSpec.symm hX
  obtain ⟨s, hs⟩ := AffineNonsingularLifting.exists_lift_of_isRegular hreg g hg hI (AlgHom.id k _)
  let ρ : E.scheme ⟶ X :=
    E.scheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s.toRingHom) ≫ X.isoSpec.inv
  have hinv : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(X, ⊤)).hom, Iso.hom_inv_id, ← Scheme.toSpecΓ_appTop,
      ← Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_toSpecΓ]
    rfl
  have hρ : ρ.appTop = CommRingCat.ofHom s.toRingHom := by
    simp only [ρ, Scheme.Hom.comp_appTop, hinv, Scheme.toSpecΓ_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality]
    exact Iso.inv_hom_id_assoc _ _
  refine ⟨ρ, ext_of_isAffine ?_, ext_of_isAffine ?_⟩
  · rw [Scheme.Hom.comp_appTop, hρ]
    ext a
    exact congr($hs a)
  · rw [Scheme.Hom.comp_appTop, hρ]
    ext c
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2 c
    exact s.commutes c

/-- **Hartshorne II, Exercise 8.7.** Let `k` be an algebraically closed field, `X` an affine
nonsingular scheme of finite type over `k`, and `F` a coherent `𝒪_X`-module. Then every
infinitesimal extension `(X', I)` of `X` by `F` is isomorphic to the trivial extension
`(X, 𝒪_X ⊕ F)`: the closed immersion `ι : X ⟶ X'` is a homeomorphism, and there is an isomorphism
of sheaves of rings `𝒪_{X'} ≅ ι_* (𝒪_X ⊕ F)` compatible with the projections onto `𝒪_X`, the
structures over `k`, and the identification `I ≅ F`. -/
theorem nonempty_trivialIso [IsAlgClosed k] [LocallyOfFiniteType pX] [IsAffine X]
    (hX : X.IsRegular) (hF : IsCoherent F) :
    IsHomeomorph E.ι.base ∧ Nonempty E.TrivialIso := by
  obtain ⟨ρ, hρ, hρk⟩ := E.exists_retraction hX hF
  have hinv : ∀ (U : E.scheme.Opensᵒᵖ) y,
      (inv (E.split ρ hρ)).app U ((E.split ρ hρ).app U y) = y := fun U y =>
    ConcreteCategory.congr_hom ((asIso (E.split ρ hρ)).hom_inv_id_app U) y
  refine ⟨E.isHomeomorph, ⟨⟨(asIso (E.split ρ hρ)).symm, ?_, ?_, ?_⟩⟩⟩
  · rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
    ext U x
    exact (E.app_splitHom ρ hρ U x).symm
  · intro c
    have : E.over.appTop c = (E.split ρ hρ).app (op ⊤) (TrivSqZeroExt.inl (pX.appTop c)) := by
      change _ = ρ.appLE (E.ι ⁻¹ᵁ ⊤) ⊤ (E.le_preimage ρ hρ ⊤) (pX.appTop c) + E.idealIncl ⊤ 0
      have h : ρ.appLE (E.ι ⁻¹ᵁ ⊤) ⊤ (E.le_preimage ρ hρ ⊤) = ρ.appTop :=
        ρ.appLE_eq_app (U := ⊤)
      rw [map_zero, add_zero, ← hρk, h]
      rfl
    rw [this]
    exact hinv _ _
  · intro U m
    have : (show Γ(E.scheme, U) from Scheme.Modules.Hom.app (closedImmersionIdealSheafι E.ι) U
        (E.iso.hom.app U m)) = (E.split ρ hρ).app (op U) (TrivSqZeroExt.inr m) := by
      change _ = ρ.appLE (E.ι ⁻¹ᵁ U) U (E.le_preimage ρ hρ U) 0 + E.idealIncl U m
      rw [map_zero, zero_add]
      rfl
    rw [this]
    exact hinv _ _

end InfinitesimalExtension

end Hartshorne
