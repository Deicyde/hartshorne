/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.CommRingCat

/-! # The relative differential sheaf and its canonical derivation -/

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The genuine inverse-image structure sheaf on the source of a scheme morphism. -/
noncomputable def inverseImageStructureSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf

/-- The structural map from `f⁻¹𝒪_Y` to `𝒪_X`, transposed from the scheme map. -/
noncomputable def inverseImageStructureSheafMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    inverseImageStructureSheaf f ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv
    Y.sheaf X.sheaf).symm (ObjectProperty.homMk f.c)

/-- The pointwise Kähler presheaf for the actual inverse-image structural map. -/
noncomputable def relativeDifferentialsPresheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (inverseImageStructureSheafMap f).hom

/-- The relative differential sheaf, obtained by module sheafification of the Kähler presheaf. -/
noncomputable def relativeDifferentials {X Y : Scheme.{u}} (f : X ⟶ Y) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeDifferentialsPresheaf f)

/-- The canonical derivation, postcomposed with the module-sheafification unit. -/
noncomputable def relativeDifferentialsDerivation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (relativeDifferentials f).val.Derivation' (inverseImageStructureSheafMap f).hom :=
  (PresheafOfModules.DifferentialsConstruction.derivation'
    (inverseImageStructureSheafMap f).hom).postcomp
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (relativeDifferentialsPresheaf f))

/-- The relative differential sheaf together with its canonical relative derivation. -/
noncomputable def relativeDifferentialsWithDerivation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Σ M : X.Modules, M.val.Derivation' (inverseImageStructureSheafMap f).hom :=
  ⟨relativeDifferentials f, relativeDifferentialsDerivation f⟩

/-- The canonical derivation as a morphism of abelian sheaves, not of `𝒪_X`-modules. -/
noncomputable def relativeDifferentialsD {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ RingCat Ab.{u})).obj X.ringCatSheaf ⟶
        (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeDifferentials f) where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom ((relativeDifferentialsDerivation f).d (X := U))
      naturality := by
        intro U V i
        ext a
        exact (relativeDifferentialsDerivation f).d_map i a }

/-- The canonical abelian-sheaf derivation satisfies Leibniz on every open. -/
theorem relativeDifferentialsD_mul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (a b : X.presheaf.obj U) :
    ((relativeDifferentialsD f).hom.app U).hom (a * b) =
      (Modules.smul (U := U.unop) (M := relativeDifferentials f) a).hom
          (((relativeDifferentialsD f).hom.app U).hom b) +
        (Modules.smul (U := U.unop) (M := relativeDifferentials f) b).hom
          (((relativeDifferentialsD f).hom.app U).hom a) :=
  (relativeDifferentialsDerivation f).d_mul a b

/-- The canonical derivation vanishes on the actual inverse-image structure sheaf. -/
theorem relativeDifferentialsD_vanishes {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (a : (inverseImageStructureSheaf f).obj.obj U) :
    ((relativeDifferentialsD f).hom.app U).hom
      ((inverseImageStructureSheafMap f).hom.app U a) = 0 :=
  (relativeDifferentialsDerivation f).d_app a

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

universe u

/-- Module-sheaf morphisms from the relative differentials correspond to relative derivations. -/
noncomputable def relativeDifferentialsHomEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) : (relativeDifferentials f ⟶ M) ≃
      M.val.Derivation' (inverseImageStructureSheafMap f).hom := by
  let φ := (inverseImageStructureSheafMap f).hom
  let δ := PresheafOfModules.DifferentialsConstruction.derivation' φ
  let hδ := PresheafOfModules.DifferentialsConstruction.isUniversal' φ
  exact (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    { toFun := δ.postcomp
      invFun := hδ.desc
      left_inv := by
        intro α
        apply hδ.postcomp_injective
        exact hδ.fac (δ.postcomp α)
      right_inv := fun d => hδ.fac d }

/-- The universal bijection is composition with the already constructed canonical derivation. -/
theorem relativeDifferentialsHomEquiv_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) (α : relativeDifferentials f ⟶ M) :
    relativeDifferentialsHomEquiv f M α =
      (relativeDifferentialsDerivation f).postcomp α.val := by
  ext U a
  rfl

/-- The universal bijection is natural in the target module sheaf. -/
theorem relativeDifferentialsHomEquiv_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : X.Modules} (α : relativeDifferentials f ⟶ M) (τ : M ⟶ N) :
    relativeDifferentialsHomEquiv f N (α ≫ τ) =
      (relativeDifferentialsHomEquiv f M α).postcomp τ.val := by
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext U a
  rfl

/-- Relative derivations with values in actual module sheaves, functorial by postcomposition. -/
noncomputable def relativeDerivationsFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.Modules ⥤ Type u where
  obj M := M.val.Derivation' (inverseImageStructureSheafMap f).hom
  map τ := ↾fun d => d.postcomp τ.val
  map_id M := by
    ext d U a
    rfl
  map_comp τ σ := by
    ext d U a
    rfl

/-- The constructed differential sheaf corepresents the concrete relative-derivation functor. -/
noncomputable def relativeDifferentialsCorepresentable {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (relativeDerivationsFunctor f).CorepresentableBy (relativeDifferentials f) where
  homEquiv := relativeDifferentialsHomEquiv f _
  homEquiv_comp τ α := relativeDifferentialsHomEquiv_naturality f α τ

/-- The universal element of this representation is the original canonical derivation. -/
theorem relativeDifferentialsCorepresentable_id {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (relativeDifferentialsCorepresentable f).homEquiv (𝟙 (relativeDifferentials f)) =
      relativeDifferentialsDerivation f := by
  change relativeDifferentialsHomEquiv f (relativeDifferentials f) _ = _
  rw [relativeDifferentialsHomEquiv_apply]
  ext U a
  rfl

/-- Every relative derivation into a module sheaf has a unique linear factorization. -/
theorem relativeDifferentials_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) (d : M.val.Derivation' (inverseImageStructureSheafMap f).hom) :
    ∃! α : relativeDifferentials f ⟶ M,
      (relativeDifferentialsDerivation f).postcomp α.val = d := by
  refine ⟨(relativeDifferentialsHomEquiv f M).symm d, ?_, ?_⟩
  · exact (relativeDifferentialsHomEquiv_apply f M _).symm.trans
      ((relativeDifferentialsHomEquiv f M).apply_symm_apply d)
  · intro α hα
    apply (relativeDifferentialsHomEquiv f M).injective
    exact (relativeDifferentialsHomEquiv_apply f M α).trans
      (hα.trans ((relativeDifferentialsHomEquiv f M).apply_symm_apply d).symm)

/-- Another universal module-sheaf pair admits a unique derivation-compatible isomorphism. -/
theorem relativeDifferentials_uniqueUpToIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : X.Modules) (r : (relativeDerivationsFunctor f).CorepresentableBy N) :
    ∃! e : relativeDifferentials f ≅ N,
      (relativeDifferentialsDerivation f).postcomp e.hom.val = r.homEquiv (𝟙 N) := by
  let e := (relativeDifferentialsCorepresentable f).uniqueUpToIso r
  have he : relativeDifferentialsHomEquiv f N e.hom = r.homEquiv (𝟙 N) := by
    change (relativeDifferentialsHomEquiv f N)
      ((relativeDifferentialsHomEquiv f N).symm (r.homEquiv (𝟙 N))) = _
    exact (relativeDifferentialsHomEquiv f N).apply_symm_apply _
  refine ⟨e, ?_, ?_⟩
  · exact (relativeDifferentialsHomEquiv_apply f N e.hom).symm.trans he
  · intro e' he'
    apply Iso.ext
    apply (relativeDifferentialsHomEquiv f N).injective
    exact (relativeDifferentialsHomEquiv_apply f N e'.hom).trans (he'.trans he.symm)

/-- The canonical differential pair represents relative derivations naturally and is unique
up to the unique isomorphism carrying its specified universal derivation. -/
theorem relativeDifferentials_universal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ r : (relativeDerivationsFunctor f).CorepresentableBy (relativeDifferentials f),
      r.homEquiv (𝟙 (relativeDifferentials f)) = relativeDifferentialsDerivation f ∧
      ∀ (N : X.Modules) (r' : (relativeDerivationsFunctor f).CorepresentableBy N),
        ∃! e : relativeDifferentials f ≅ N,
          (relativeDifferentialsDerivation f).postcomp e.hom.val = r'.homEquiv (𝟙 N) :=
  ⟨relativeDifferentialsCorepresentable f, relativeDifferentialsCorepresentable_id f,
    relativeDifferentials_uniqueUpToIso f⟩

end AlgebraicGeometry.Scheme
