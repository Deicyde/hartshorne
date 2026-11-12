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

instance : IsCentralScalar R M := ⟨fun _ _ => rfl⟩

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

end Ring

attribute [local instance] opModule

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

attribute [local instance] InfinitesimalExtension.isClosedImmersion

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

end InfinitesimalExtension

end Hartshorne
