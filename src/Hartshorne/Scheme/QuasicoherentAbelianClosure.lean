/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Hartshorne.Scheme.AffineGlobalSectionsExact
import Hartshorne.Scheme.AffineTildeLocalization

/-!
# Quasi-coherent and coherent modules form abelian subcategories

Hartshorne, *Algebraic Geometry*, II.5, Proposition 5.7, pp. 114–115.

Let `X` be a scheme. For a morphism `f : F ⟶ G` of quasi-coherent `𝒪_X`-modules, the kernel,
the image and the cokernel of `f` are quasi-coherent, and an extension of quasi-coherent
`𝒪_X`-modules is quasi-coherent. Consequently the quasi-coherent modules form a full abelian
subcategory of `X.Modules`, whose inclusion is exact (kernels and cokernels are computed in
`X.Modules`). If `X` is locally Noetherian, the same holds for coherent modules.

The proof is affine-local. Restriction along an open immersion is exact. On `Spec A`, a
morphism between modules of the form `M̃` and `Ñ` is `φ̃` for a linear map `φ`, and tilde is
exact, so kernels and cokernels are `(ker φ)~` and `(coker φ)~`. For an extension
`0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` on `Spec A` with `F'` and `F''` quasi-coherent, the global sections
form a short exact sequence (Hartshorne II.5.6), and the short five lemma applied to the
canonical map from the tilde of this sequence shows that `Γ(F)~ ⟶ F` is an isomorphism. In
the Noetherian case, submodules, quotients and extensions of finitely generated modules are
finitely generated.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

namespace QuasicoherentAbelianAux

/-! ### Restriction along an open immersion is exact -/

/-- Restriction of module sheaves along an open immersion preserves limits. -/
instance restrictFunctor_preservesLimits {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    PreservesLimits (Scheme.Modules.restrictFunctor f) := by
  have : ReflectsLimits (Scheme.Modules.toPresheaf Y) := reflectsLimits_of_reflectsIsomorphisms
  have : PreservesLimits (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf Y) := by
    apply preservesLimits_of_evaluation
    intro U
    have : PreservesLimits
        ((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op (f ''ᵁ U.unop))) :=
      evaluationPreservesLimits _
    have : PreservesLimits (Scheme.Modules.toPresheaf X ⋙
        (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op (f ''ᵁ U.unop))) :=
      comp_preservesLimits _ _
    exact preservesLimits_of_natIso (F := Scheme.Modules.toPresheaf X ⋙
      (evaluation _ _).obj (Opposite.op (f ''ᵁ U.unop))) (Iso.refl _)
  exact preservesLimits_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf Y)

/-- Restriction to an affine open `U`, viewed on `Spec Γ(X, U)`. -/
abbrev specRestrictFunctor {X : Scheme.{u}} (U : X.affineOpens) :
    X.Modules ⥤ (Spec Γ(X, (U : X.Opens))).Modules :=
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  Scheme.Modules.restrictFunctor U.2.fromSpec

/-! ### The affine case -/

variable {R : CommRingCat.{u}}

instance moduleSpecΓFunctor_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (C := (Spec R).Modules) (moduleSpecΓFunctor (R := R)) :=
  @Functor.preservesZeroMorphisms_of_isRightAdjoint _ _ _ _ _ _ _ tilde.adjunction.isRightAdjoint

/-- On `Spec R`, the kernel of a morphism between modules associated to `M` and `N` is
associated to the kernel of the corresponding linear map. -/
def kernelTildeIso {M N : ModuleCat.{u} R} {F G : (Spec R).Modules}
    (eF : (tilde.functor R).obj M ≅ F) (eG : (tilde.functor R).obj N ≅ G) (f : F ⟶ G) :
    (tilde.functor R).obj (kernel ((tilde.functor R).preimage (eF.hom ≫ f ≫ eG.inv))) ≅
      kernel f :=
  haveI := affineTilde_preservesFiniteLimits R
  PreservesKernel.iso (tilde.functor R) _ ≪≫ kernel.mapIso _ _ eF eG (by
    rw [Functor.map_preimage]
    simp)

/-- On `Spec R`, the cokernel of a morphism between modules associated to `M` and `N` is
associated to the cokernel of the corresponding linear map. -/
def cokernelTildeIso {M N : ModuleCat.{u} R} {F G : (Spec R).Modules}
    (eF : (tilde.functor R).obj M ≅ F) (eG : (tilde.functor R).obj N ≅ G) (f : F ⟶ G) :
    (tilde.functor R).obj (cokernel ((tilde.functor R).preimage (eF.hom ≫ f ≫ eG.inv))) ≅
      cokernel f :=
  PreservesCokernel.iso (tilde.functor R) _ ≪≫ cokernel.mapIso _ _ eF eG (by
    rw [Functor.map_preimage]
    simp)

theorem essImage_kernel {F G : (Spec R).Modules} (f : F ⟶ G)
    (hF : (tilde.functor R).essImage F) (hG : (tilde.functor R).essImage G) :
    (tilde.functor R).essImage (kernel f) :=
  ⟨_, ⟨kernelTildeIso hF.getIso hG.getIso f⟩⟩

theorem essImage_cokernel {F G : (Spec R).Modules} (f : F ⟶ G)
    (hF : (tilde.functor R).essImage F) (hG : (tilde.functor R).essImage G) :
    (tilde.functor R).essImage (cokernel f) :=
  ⟨_, ⟨cokernelTildeIso hF.getIso hG.getIso f⟩⟩

/-- Module sheaves on `Spec R` associated to finitely generated `R`-modules. -/
def IsFiniteTilde (F : (Spec R).Modules) : Prop :=
  ∃ M : ModuleCat.{u} R, Module.Finite R M ∧ Nonempty ((tilde.functor R).obj M ≅ F)

theorem isFiniteTilde_kernel [IsNoetherianRing R] {F G : (Spec R).Modules} (f : F ⟶ G)
    (hF : IsFiniteTilde F) (hG : IsFiniteTilde G) : IsFiniteTilde (kernel f) := by
  obtain ⟨M, hM, ⟨eF⟩⟩ := hF
  obtain ⟨N, -, ⟨eG⟩⟩ := hG
  refine ⟨_, ?_, ⟨kernelTildeIso eF eG f⟩⟩
  exact Module.Finite.of_injective
    (kernel.ι ((tilde.functor R).preimage (eF.hom ≫ f ≫ eG.inv))).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

theorem isFiniteTilde_cokernel {F G : (Spec R).Modules} (f : F ⟶ G)
    (hF : IsFiniteTilde F) (hG : IsFiniteTilde G) : IsFiniteTilde (cokernel f) := by
  obtain ⟨M, -, ⟨eF⟩⟩ := hF
  obtain ⟨N, hN, ⟨eG⟩⟩ := hG
  refine ⟨_, ?_, ⟨cokernelTildeIso eF eG f⟩⟩
  exact Module.Finite.of_surjective
    (cokernel.π ((tilde.functor R).preimage (eF.hom ≫ f ≫ eG.inv))).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

theorem isFiniteTilde_of_isZero {F : (Spec R).Modules} (hF : IsZero F) : IsFiniteTilde F :=
  ⟨ModuleCat.of R PUnit, inferInstance,
    ⟨IsZero.iso ((tilde.functor R).map_isZero (ModuleCat.isZero_of_subsingleton _)) hF⟩⟩

/-- On `Spec R`, global sections (as `R`-modules) of a short exact sequence whose first term is
quasi-coherent form a short exact sequence (Hartshorne II.5.6). -/
theorem shortExact_map_moduleSpecΓ (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] : (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  have h := affine_globalSections_shortExact S hS
  have hex := (ShortComplex.moduleCat_exact_iff _).mp h.exact
  have hmono := (ModuleCat.mono_iff_injective _).mp h.mono_f
  have hepi := (ModuleCat.epi_iff_surjective _).mp h.epi_g
  exact
    { exact := (ShortComplex.moduleCat_exact_iff _).mpr fun x hx ↦ hex x hx
      mono_f := (ModuleCat.mono_iff_injective _).mpr hmono
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hepi }

/-- On `Spec R`, an extension of quasi-coherent modules is canonically associated to its
global sections. -/
theorem isIso_fromTildeΓ_of_shortExact (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : IsIso S.X₂.fromTildeΓ := by
  have h₁ := shortExact_map_moduleSpecΓ S hS
  have h₂ : ((S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R)).ShortExact :=
    (affineTilde_exact R).2.1 (S.map (moduleSpecΓFunctor (R := R))) h₁
  let φ : (S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R) ⟶ S :=
    { τ₁ := S.X₁.fromTildeΓ
      τ₂ := S.X₂.fromTildeΓ
      τ₃ := S.X₃.fromTildeΓ
      comm₁₂ := (Scheme.Modules.fromTildeΓNatTrans.naturality S.f).symm
      comm₂₃ := (Scheme.Modules.fromTildeΓNatTrans.naturality S.g).symm }
  have : IsIso φ.τ₁ := inferInstanceAs (IsIso S.X₁.fromTildeΓ)
  have : IsIso φ.τ₃ := inferInstanceAs (IsIso S.X₃.fromTildeΓ)
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ h₂ hS

theorem isQuasicoherent_of_shortExact_spec (S : ShortComplex (Spec R).Modules)
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent := by
  have := isIso_fromTildeΓ_of_shortExact S hS
  exact (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr this

theorem isFiniteTilde_of_shortExact (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    (h₁ : IsFiniteTilde S.X₁) (h₃ : IsFiniteTilde S.X₃) : IsFiniteTilde S.X₂ := by
  obtain ⟨M₁, hM₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨M₃, hM₃, ⟨e₃⟩⟩ := h₃
  have : S.X₁.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e₁
      (show ((tilde.functor R).obj M₁).IsQuasicoherent from inferInstance)
  have : S.X₃.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e₃
      (show ((tilde.functor R).obj M₃).IsQuasicoherent from inferInstance)
  have hiso := isIso_fromTildeΓ_of_shortExact S hS
  refine ⟨moduleSpecΓFunctor.obj S.X₂, ?_, ⟨@asIso _ _ _ _ _ hiso⟩⟩
  have h := shortExact_map_moduleSpecΓ S hS
  have : Module.Finite R ((𝟭 (ModuleCat R)).obj M₁) := hM₁
  have : Module.Finite R ((𝟭 (ModuleCat R)).obj M₃) := hM₃
  have : Module.Finite R (S.map (moduleSpecΓFunctor (R := R))).X₁ :=
    Module.Finite.equiv ((tilde.toTildeΓNatIso.app M₁) ≪≫
      moduleSpecΓFunctor.mapIso e₁).toLinearEquiv
  have : Module.Finite R (S.map (moduleSpecΓFunctor (R := R))).X₃ :=
    Module.Finite.equiv ((tilde.toTildeΓNatIso.app M₃) ≪≫
      moduleSpecΓFunctor.mapIso e₃).toLinearEquiv
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact
  exact Module.Finite.of_exact hex ((ModuleCat.epi_iff_surjective _).mp h.epi_g)

/-! ### Globalization -/

variable {X : Scheme.{u}}

theorem isQuasicoherent_iff_forall_essImage (F : X.Modules) :
    F.IsQuasicoherent ↔
      ∀ U : X.affineOpens, (tilde.functor Γ(X, (U : X.Opens))).essImage (specRestriction F U) := by
  refine ⟨fun h U ↦ ?_, fun h ↦ ?_⟩
  · have h' := ((quasicoherent_affine_local_tfae F).out 0 2).mp h
    exact isIso_fromTildeΓ_iff.mp (h' U)
  · have h' : HasAffineTildeCover F := ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, h⟩
    exact ((quasicoherent_affine_local_tfae F).out 0 1).mpr h'

theorem isCoherent_iff_forall_isFiniteTilde [IsLocallyNoetherian X] (F : X.Modules) :
    IsCoherent F ↔ ∀ U : X.affineOpens, IsFiniteTilde (specRestriction F U) :=
  (coherent_affine_local_tfae F).out 0 2

theorem isNoetherianRing_affineOpen [IsLocallyNoetherian X] (U : X.affineOpens) :
    IsNoetherianRing Γ(X, (U : X.Opens)) :=
  IsLocallyNoetherian.component_noetherian U

/-- Restriction to an affine open commutes with kernels. -/
def specRestrictionKernelIso {F G : X.Modules} (f : F ⟶ G) (U : X.affineOpens) :
    specRestriction (kernel f) U ≅ kernel ((specRestrictFunctor U).map f) :=
  PreservesKernel.iso (specRestrictFunctor U) f

/-- Restriction to an affine open commutes with cokernels. -/
def specRestrictionCokernelIso {F G : X.Modules} (f : F ⟶ G) (U : X.affineOpens) :
    specRestriction (cokernel f) U ≅ cokernel ((specRestrictFunctor U).map f) :=
  PreservesCokernel.iso (specRestrictFunctor U) f

theorem shortExact_specRestrict {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (U : X.affineOpens) : (S.map (specRestrictFunctor U)).ShortExact :=
  hS.map_of_exact (specRestrictFunctor U)

theorem isFiniteTilde_specRestriction_of_isZero {F : X.Modules} (hF : IsZero F)
    (U : X.affineOpens) : IsFiniteTilde (specRestriction F U) :=
  isFiniteTilde_of_isZero ((specRestrictFunctor U).map_isZero hF)

/-! ### Closure properties of object properties in an abelian category -/

section ObjectProperty

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C)

theorem isClosedUnderKernels_of_prop_kernel [P.IsClosedUnderIsomorphisms]
    (h : ∀ {A B : C} (f : A ⟶ B), P A → P B → P (kernel f)) : P.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨hA, hB⟩⟩
    exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk) (h f hA hB)

theorem isClosedUnderCokernels_of_prop_cokernel [P.IsClosedUnderIsomorphisms]
    (h : ∀ {A B : C} (f : A ⟶ B), P A → P B → P (cokernel f)) : P.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨hA, hB⟩⟩
    exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (h f hA hB)

/-- A property containing zero and closed under isomorphisms and extensions is closed under
finite products (binary products are split extensions). -/
theorem isClosedUnderFiniteProducts_of_isClosedUnderExtensions [P.IsClosedUnderIsomorphisms]
    [P.ContainsZero] [P.IsClosedUnderExtensions] : P.IsClosedUnderFiniteProducts := by
  have : P.IsClosedUnderBinaryProducts := ⟨by
    rintro A ⟨p⟩
    exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
      (P.prop_biprod (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))⟩
  exact .mk'

theorem preservesFiniteLimits_ι [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts] : PreservesFiniteLimits P.ι := by
  have := fun {A B : P.FullSubcategory} (f : A ⟶ B) ↦ P.preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

theorem preservesFiniteColimits_ι [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts] : PreservesFiniteColimits P.ι := by
  have := fun {A B : P.FullSubcategory} (f : A ⟶ B) ↦ P.preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

end ObjectProperty

end QuasicoherentAbelianAux

open QuasicoherentAbelianAux

variable {X : Scheme.{u}}

/-! ### Quasi-coherent modules -/

/-- **Hartshorne II.5.7 (kernels).** The kernel of a morphism of quasi-coherent
`𝒪_X`-modules is quasi-coherent. -/
theorem isQuasicoherent_kernel {F G : X.Modules} (f : F ⟶ G) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : (kernel f).IsQuasicoherent := by
  have hF := (isQuasicoherent_iff_forall_essImage F).mp ‹_›
  have hG := (isQuasicoherent_iff_forall_essImage G).mp ‹_›
  refine (isQuasicoherent_iff_forall_essImage _).mpr fun U ↦ ?_
  exact (tilde.functor _).essImage.prop_of_iso (specRestrictionKernelIso f U).symm
    (essImage_kernel _ (hF U) (hG U))

/-- **Hartshorne II.5.7 (cokernels).** The cokernel of a morphism of quasi-coherent
`𝒪_X`-modules is quasi-coherent. -/
theorem isQuasicoherent_cokernel {F G : X.Modules} (f : F ⟶ G) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : (cokernel f).IsQuasicoherent := by
  have hF := (isQuasicoherent_iff_forall_essImage F).mp ‹_›
  have hG := (isQuasicoherent_iff_forall_essImage G).mp ‹_›
  refine (isQuasicoherent_iff_forall_essImage _).mpr fun U ↦ ?_
  exact (tilde.functor _).essImage.prop_of_iso (specRestrictionCokernelIso f U).symm
    (essImage_cokernel _ (hF U) (hG U))

/-- **Hartshorne II.5.7 (images).** The image of a morphism of quasi-coherent
`𝒪_X`-modules is quasi-coherent. -/
theorem isQuasicoherent_image {F G : X.Modules} (f : F ⟶ G) [F.IsQuasicoherent]
    [G.IsQuasicoherent] : (image f).IsQuasicoherent := by
  have := isQuasicoherent_cokernel f
  have := isQuasicoherent_kernel (cokernel.π f)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (Abelian.imageIsoImage f) this

/-- **Hartshorne II.5.7 (extensions).** An extension of quasi-coherent `𝒪_X`-modules is
quasi-coherent. -/
theorem isQuasicoherent_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  rw [isQuasicoherent_iff_forall_essImage]
  intro U
  have h₁ := (isQuasicoherent_iff_forall_essImage S.X₁).mp ‹_› U
  have h₃ := (isQuasicoherent_iff_forall_essImage S.X₃).mp ‹_› U
  rw [essImage_tilde] at h₁ h₃ ⊢
  have : (S.map (specRestrictFunctor U)).X₁.IsQuasicoherent := h₁
  have : (S.map (specRestrictFunctor U)).X₃.IsQuasicoherent := h₃
  exact isQuasicoherent_of_shortExact_spec _ (shortExact_specRestrict hS U)

theorem isQuasicoherent_of_isZero {F : X.Modules} (hF : IsZero F) : F.IsQuasicoherent :=
  (isQuasicoherent_iff_forall_essImage F).mpr fun U ↦
    have ⟨M, _, ⟨e⟩⟩ := isFiniteTilde_specRestriction_of_isZero hF U
    ⟨M, ⟨e⟩⟩

/-! ### The abelian subcategory of quasi-coherent modules -/

instance isQuasicoherent_containsZero :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero :=
  ⟨(HasZeroObject.zero (C := X.Modules)).elim fun Z hZ ↦ ⟨Z, hZ, isQuasicoherent_of_isZero hZ⟩⟩

instance isQuasicoherent_isClosedUnderKernels :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels :=
  isClosedUnderKernels_of_prop_kernel _ fun {A B} f (_ : A.IsQuasicoherent) (_ : B.IsQuasicoherent) ↦
    isQuasicoherent_kernel f

instance isQuasicoherent_isClosedUnderCokernels :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels :=
  isClosedUnderCokernels_of_prop_cokernel _ fun {A B} f (_ : A.IsQuasicoherent) (_ : B.IsQuasicoherent) ↦
    isQuasicoherent_cokernel f

instance isQuasicoherent_isClosedUnderExtensions :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ :=
    haveI : S.X₁.IsQuasicoherent := h₁
    haveI : S.X₃.IsQuasicoherent := h₃
    isQuasicoherent_of_shortExact hS

instance isQuasicoherent_isClosedUnderFiniteProducts :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteProducts :=
  isClosedUnderFiniteProducts_of_isClosedUnderExtensions _

/-- **Hartshorne II.5.7.** The quasi-coherent `𝒪_X`-modules form an abelian category. -/
instance quasicoherentModulesAbelian :
    Abelian (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  inferInstance

/-- The inclusion of quasi-coherent modules into `𝒪_X`-modules preserves finite limits. -/
instance quasicoherentModules_ι_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
  preservesFiniteLimits_ι _

/-- The inclusion of quasi-coherent modules into `𝒪_X`-modules preserves finite colimits. -/
instance quasicoherentModules_ι_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
  preservesFiniteColimits_ι _

/-! ### Coherent modules on a locally Noetherian scheme -/

theorem isCoherent_of_iso {F G : X.Modules} (e : F ≅ G) (hF : IsCoherent F) : IsCoherent G := by
  obtain ⟨ι, U, hU, h⟩ := hF
  exact ⟨ι, U, hU, fun i ↦ (h i).imp fun M ⟨hM, ⟨e'⟩⟩ ↦
    ⟨hM, ⟨e' ≪≫ (specRestrictFunctor (U i)).mapIso e⟩⟩⟩

theorem isCoherent_of_isZero {F : X.Modules} (hF : IsZero F) : IsCoherent F :=
  ⟨X.affineOpens, id, iSup_affineOpens_eq_top X,
    fun U ↦ isFiniteTilde_specRestriction_of_isZero hF U⟩

/-- **Hartshorne II.5.7 (kernels, coherent case).** On a locally Noetherian scheme, the kernel
of a morphism of coherent `𝒪_X`-modules is coherent. -/
theorem isCoherent_kernel [IsLocallyNoetherian X] {F G : X.Modules} (f : F ⟶ G)
    (hF : IsCoherent F) (hG : IsCoherent G) : IsCoherent (kernel f) := by
  rw [isCoherent_iff_forall_isFiniteTilde] at hF hG ⊢
  intro U
  have := isNoetherianRing_affineOpen U
  obtain ⟨M, hM, ⟨e⟩⟩ := isFiniteTilde_kernel _ (hF U) (hG U)
  exact ⟨M, hM, ⟨e ≪≫ (specRestrictionKernelIso f U).symm⟩⟩

/-- **Hartshorne II.5.7 (cokernels, coherent case).** On a locally Noetherian scheme, the
cokernel of a morphism of coherent `𝒪_X`-modules is coherent. -/
theorem isCoherent_cokernel [IsLocallyNoetherian X] {F G : X.Modules} (f : F ⟶ G)
    (hF : IsCoherent F) (hG : IsCoherent G) : IsCoherent (cokernel f) := by
  rw [isCoherent_iff_forall_isFiniteTilde] at hF hG ⊢
  intro U
  obtain ⟨M, hM, ⟨e⟩⟩ := isFiniteTilde_cokernel _ (hF U) (hG U)
  exact ⟨M, hM, ⟨e ≪≫ (specRestrictionCokernelIso f U).symm⟩⟩

/-- **Hartshorne II.5.7 (images, coherent case).** On a locally Noetherian scheme, the image of
a morphism of coherent `𝒪_X`-modules is coherent. -/
theorem isCoherent_image [IsLocallyNoetherian X] {F G : X.Modules} (f : F ⟶ G)
    (hF : IsCoherent F) (hG : IsCoherent G) : IsCoherent (image f) :=
  isCoherent_of_iso (Abelian.imageIsoImage f)
    (isCoherent_kernel _ hG (isCoherent_cokernel f hF hG))

/-- **Hartshorne II.5.7 (extensions, coherent case).** On a locally Noetherian scheme, an
extension of coherent `𝒪_X`-modules is coherent. -/
theorem isCoherent_of_shortExact [IsLocallyNoetherian X] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h₁ : IsCoherent S.X₁) (h₃ : IsCoherent S.X₃) : IsCoherent S.X₂ := by
  rw [isCoherent_iff_forall_isFiniteTilde] at h₁ h₃ ⊢
  exact fun U ↦ isFiniteTilde_of_shortExact _ (shortExact_specRestrict hS U) (h₁ U) (h₃ U)

variable (X) in
/-- The coherent `𝒪_X`-modules, as a property of objects of `X.Modules`. -/
def coherentModules : ObjectProperty X.Modules := fun F ↦ IsCoherent F

instance coherentModules_isClosedUnderIsomorphisms :
    (coherentModules X).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ isCoherent_of_iso e h⟩

instance coherentModules_containsZero : (coherentModules X).ContainsZero :=
  ⟨(HasZeroObject.zero (C := X.Modules)).elim fun Z hZ ↦ ⟨Z, hZ, isCoherent_of_isZero hZ⟩⟩

instance coherentModules_isClosedUnderKernels [IsLocallyNoetherian X] :
    (coherentModules X).IsClosedUnderKernels :=
  isClosedUnderKernels_of_prop_kernel _ fun f hF hG ↦ isCoherent_kernel f hF hG

instance coherentModules_isClosedUnderCokernels [IsLocallyNoetherian X] :
    (coherentModules X).IsClosedUnderCokernels :=
  isClosedUnderCokernels_of_prop_cokernel _ fun f hF hG ↦ isCoherent_cokernel f hF hG

instance coherentModules_isClosedUnderExtensions [IsLocallyNoetherian X] :
    (coherentModules X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := isCoherent_of_shortExact hS h₁ h₃

instance coherentModules_isClosedUnderFiniteProducts [IsLocallyNoetherian X] :
    (coherentModules X).IsClosedUnderFiniteProducts :=
  isClosedUnderFiniteProducts_of_isClosedUnderExtensions _

/-- **Hartshorne II.5.7 (coherent case).** On a locally Noetherian scheme, the coherent
`𝒪_X`-modules form an abelian category. -/
instance coherentModulesAbelian [IsLocallyNoetherian X] :
    Abelian (coherentModules X).FullSubcategory :=
  inferInstance

/-- On a locally Noetherian scheme, the inclusion of coherent modules into `𝒪_X`-modules
preserves finite limits. -/
instance coherentModules_ι_preservesFiniteLimits [IsLocallyNoetherian X] :
    PreservesFiniteLimits (coherentModules X).ι :=
  preservesFiniteLimits_ι _

/-- On a locally Noetherian scheme, the inclusion of coherent modules into `𝒪_X`-modules
preserves finite colimits. -/
instance coherentModules_ι_preservesFiniteColimits [IsLocallyNoetherian X] :
    PreservesFiniteColimits (coherentModules X).ι :=
  preservesFiniteColimits_ι _

end

end Hartshorne
