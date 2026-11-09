/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ConstantSheaf
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# The constant sheaf is the sheafification of the constant presheaf

Hartshorne, *Algebraic Geometry*, Example II.1.0.3 (p. 62).

The constant sheaf `Hartshorne.constantSheaf X A` of locally constant maps to `A` is canonically
isomorphic to Mathlib's constant sheaf `CategoryTheory.constantSheaf`, the sheafification of the
constant presheaf with value `A`. The comparison is the sheafification of the presheaf map sending
an element of `A` to the corresponding constant function; this map is locally injective and
locally surjective, hence becomes an isomorphism after sheafification.
-/

namespace Hartshorne

open CategoryTheory TopologicalSpace Opposite

universe u

/-- The presheaf map from the constant presheaf with value `A` to the constant sheaf of locally
constant maps, sending an element of `A` to the corresponding constant function. -/
def constToConstantSheaf (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶ (constantSheaf X A).obj where
  app U := AddCommGrpCat.ofHom (LocallyConstant.constAddMonoidHom (X := U.unop))
  naturality _ _ _ := by
    ext a
    rfl

/-- The image of `a` under the comparison map is the constant function with value `a`. -/
lemma constToConstantSheaf_app_apply (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (U : (Opens X)ᵒᵖ)
    (a : A) (x : U.unop) :
    (show LocallyConstant U.unop A from (constToConstantSheaf X A).app U a) x = a :=
  rfl

instance (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (constToConstantSheaf X A) where
  equalizerSieve_mem {U} a b h := by
    intro x hx
    refine ⟨U.unop, 𝟙 _, ?_, hx⟩
    have hab : a = b := LocallyConstant.congr_fun h ⟨x, hx⟩
    simp [hab]

instance (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (constToConstantSheaf X A) where
  imageSieve_mem {U} s := by
    intro x hx
    let s' : LocallyConstant U A := s
    let V : Opens X := ⟨Subtype.val '' (s' ⁻¹' {s' ⟨x, hx⟩}),
      U.isOpen.isOpenMap_subtype_val _ (s'.isLocallyConstant _)⟩
    have hVU : V ≤ U := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    refine ⟨V, homOfLE hVU, ⟨s' ⟨x, hx⟩, ?_⟩, ⟨⟨x, hx⟩, rfl, rfl⟩⟩
    apply LocallyConstant.ext
    rintro ⟨y, hy⟩
    obtain ⟨z, hz, rfl⟩ := hy
    exact hz.symm

/-- The constant sheaf of Hartshorne II.1.0.3 (locally constant maps to `A`) is canonically
isomorphic to Mathlib's constant sheaf, the sheafification of the constant presheaf with value
`A`. The inverse is the map out of the sheafification induced by sending an element of `A` to the
constant function. This comparison supplements Hartshorne's definition. -/
noncomputable def constantSheafIsoSheafification (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    constantSheaf X A ≅
      (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A :=
  letI f : (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A ⟶
      constantSheaf X A :=
    ⟨sheafifyLift _ (constToConstantSheaf X A) (constantSheaf X A).property⟩
  haveI fac : toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A) ≫
      f.hom = constToConstantSheaf X A :=
    toSheafify_sheafifyLift _ _ _
  haveI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f.hom :=
    @Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ fac _ (Presheaf.isLocallySurjective_toSheafify' _ _)
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ fac
  haveI : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).1 ⟨inferInstance, inferInstance⟩
  (asIso f).symm

/-- The comparison isomorphism is characterized by its inverse restricting, along the unit of
sheafification, to the map sending an element of `A` to the constant function. -/
lemma toSheafify_constantSheafIsoSheafification_inv (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    toSheafify (Opens.grothendieckTopology X) _ ≫ (constantSheafIsoSheafification X A).inv.hom =
      constToConstantSheaf X A :=
  toSheafify_sheafifyLift _ _ _

/-- The comparison isomorphism sends the image in the sheafification of an element `a` of `A`
to the constant function with value `a`. -/
lemma constantSheafIsoSheafification_inv_app_toSheafify_app (X : TopCat.{u})
    (A : AddCommGrpCat.{u}) (U : (Opens X)ᵒᵖ) (a : A) :
    (constantSheafIsoSheafification X A).inv.hom.app U
      ((toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A)).app U a) =
      (constToConstantSheaf X A).app U a :=
  congrArg (fun g ↦ g.app U a) (toSheafify_constantSheafIsoSheafification_inv X A)

end Hartshorne
