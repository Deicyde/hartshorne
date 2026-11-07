/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ResolutionToInjectiveComparison
import Hartshorne.Weil.ConstantTorsionEtaleSheaf
import Hartshorne.Weil.EtaleInverseImage
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Torsion étale cohomology

For a scheme `X : Scheme.{u}`, the category `Sheaf X.smallEtaleTopology Ab.{u}`
of abelian sheaves on the small étale site is a Grothendieck abelian category
(Mathlib, via the essentially small affine étale site), so it has enough
injectives and hence injective resolutions.  The global sections functor
`Sheaf.Γ` (the right adjoint of the constant sheaf functor) is additive, and we
define `H^i_et(X, ℤ/ℓ^r)` as its `i`-th right derived functor evaluated at the
constant sheaf `ZMod (ℓ ^ r)`.

A morphism of schemes `f : X ⟶ Y` acts through the inverse image `f⁻¹` of abelian sheaves on
the small étale sites (`Hartshorne.Weil.EtaleInverseImage`), which is exact.  For a sheaf `F` on
`Y`, apply `f⁻¹` to an injective resolution `F → I•`: the result is a resolution of `f⁻¹ F`, so it
maps to the chosen injective resolution `f⁻¹ F → J•` compatibly with the augmentations.  The
adjoint cochain map `I• ⟶ f_* J•`, followed by `Γ(Y, f_* -) = Γ(X, -)`, induces
`H^i_et(Y, F) ⟶ H^i_et(X, f⁻¹ F)`.  Since `f⁻¹` of a constant sheaf is constant, this gives
`H^i_et(Y, ℤ/ℓ^r) ⟶ H^i_et(X, ℤ/ℓ^r)`.

## Universes

The sheaf category has morphisms in `Type (u + 1)`, because the small étale
site `X.Etale` is a large category, but the global sections functor lands in
`Ab.{u}`, so the cohomology groups are `u`-small abelian groups.
-/

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

universe u

/-- The global sections functor on abelian sheaves on the small étale site is
additive: it is a right adjoint, so it preserves binary products. -/
instance additive_sheafΓ_smallEtaleTopology (X : Scheme.{u}) :
    (Sheaf.Γ X.smallEtaleTopology Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Torsion étale cohomology `H^i_et(X, ℤ/ℓ^r)`: the `i`-th right derived
functor of global sections on abelian sheaves on the small étale site of `X`,
evaluated at the constant sheaf `ZMod (ℓ ^ r)`. -/
noncomputable def torsionEtaleCohomology (X : Scheme.{u}) (ℓ r i : ℕ) : Ab.{u} :=
  ((Sheaf.Γ X.smallEtaleTopology Ab.{u}).rightDerived i).obj
    (X.constantTorsionEtaleSheaf ℓ r)

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Sheaf Y.smallEtaleTopology Ab.{u})

/-- The inverse image of the augmentation `F ⟶ I•` of the chosen injective resolution of `F`. -/
noncomputable def etaleInverseImageResolutionAugmentation :
    (CochainComplex.single₀ _).obj ((etaleInverseImage f).obj F) ⟶
      ((etaleInverseImage f).mapHomologicalComplex _).obj (injectiveResolution F).cocomplex :=
  ((HomologicalComplex.singleMapHomologicalComplex (etaleInverseImage f)
    (ComplexShape.up ℕ) 0).app F).inv ≫
      ((etaleInverseImage f).mapHomologicalComplex _).map (injectiveResolution F).ι

/-- The inverse image is exact, so it sends an injective resolution to a resolution. -/
instance : QuasiIso (etaleInverseImageResolutionAugmentation f F) := by
  unfold etaleInverseImageResolutionAugmentation
  infer_instance

/-- A comparison map, compatible with the augmentations, from the inverse image of the
injective resolution of `F` to the chosen injective resolution of `f⁻¹ F`. -/
noncomputable def etaleInverseImageComparison :
    ((etaleInverseImage f).mapHomologicalComplex _).obj (injectiveResolution F).cocomplex ⟶
      (injectiveResolution ((etaleInverseImage f).obj F)).cocomplex :=
  (Hartshorne.resolutionToInjectiveComparison_exists_uniqueUpToHomotopy
    (etaleInverseImageResolutionAugmentation f F) _).1.some.1

/-- The cochain map `I• ⟶ f_* J•` adjoint to `etaleInverseImageComparison`. -/
noncomputable def etaleCohomologyPullbackCochainMap :
    (injectiveResolution F).cocomplex ⟶ ((etalePushforward f).mapHomologicalComplex _).obj
      (injectiveResolution ((etaleInverseImage f).obj F)).cocomplex where
  f n := (Functor.sheafAdjunctionContinuous _ _ _ _).homEquiv _ _
    (by exact (etaleInverseImageComparison f F).f n)
  comm' i j _ := by
    let adj := Functor.sheafAdjunctionContinuous (etaleBaseChange f) Ab.{u}
      Y.smallEtaleTopology X.smallEtaleTopology
    let φ := etaleInverseImageComparison f F
    let I := (injectiveResolution F).cocomplex
    let J := (injectiveResolution ((etaleInverseImage f).obj F)).cocomplex
    have h1 := adj.homEquiv_naturality_right (X := I.X i) (by exact φ.f i) (J.d i j)
    have h2 := adj.homEquiv_naturality_left (I.d i j) (Y := J.X j) (by exact φ.f j)
    have h3 : (etaleInverseImage f).map (I.d i j) ≫ φ.f j = φ.f i ≫ J.d i j := (φ.comm i j).symm
    exact h1.symm.trans ((congrArg _ h3.symm).trans h2)

/-- The pullback map `H^i_et(Y, F) ⟶ H^i_et(X, f⁻¹ F)` induced by `f : X ⟶ Y`. -/
noncomputable def etaleCohomologyPullback (i : ℕ) :
    ((Sheaf.Γ Y.smallEtaleTopology Ab.{u}).rightDerived i).obj F ⟶
      ((Sheaf.Γ X.smallEtaleTopology Ab.{u}).rightDerived i).obj ((etaleInverseImage f).obj F) :=
  ((injectiveResolution F).isoRightDerivedObj (Sheaf.Γ _ _) i).hom ≫
    (HomologicalComplex.homologyFunctor _ _ i).map
      (((Sheaf.Γ _ _).mapHomologicalComplex _).map (etaleCohomologyPullbackCochainMap f F) ≫
        ((Functor.mapHomologicalComplexCompIso (etalePushforwardCompΓ f) _).hom.app _)) ≫
    ((injectiveResolution _).isoRightDerivedObj (Sheaf.Γ _ _) i).inv

/-- The pullback map `H^i_et(Y, ℤ/ℓ^r) ⟶ H^i_et(X, ℤ/ℓ^r)` induced by `f : X ⟶ Y`: the
pullback to `H^i_et(X, f⁻¹ ℤ/ℓ^r)`, followed by the identification of `f⁻¹` of the constant
sheaf with the constant sheaf. -/
noncomputable def torsionEtaleCohomologyPullback (ℓ r i : ℕ) :
    Y.torsionEtaleCohomology ℓ r i ⟶ X.torsionEtaleCohomology ℓ r i :=
  etaleCohomologyPullback f _ i ≫ ((Sheaf.Γ _ _).rightDerived i).map
    ((constantSheafCompEtaleInverseImageIso f).hom.app _)

end Pullback

end AlgebraicGeometry.Scheme
