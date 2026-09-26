/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.Basic
import Hartshorne.Nonsingular.IntrinsicNonsingular
import Hartshorne.Rational.RationalMap
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The three categories of curves

Hartshorne, *Algebraic Geometry*, I.6, Corollary 6.12 (pp. 45--46).

This file packages the objects of the three categories occurring in the
corollary.  A geometric object remembers a finite-dimensional projective
presentation, rather than an abstract variety together with a proposition
saying that some presentation exists.  Projective curves have dominant
everywhere-defined morphisms; quasi-projective curves have dominant rational
maps.  The algebraic category is the full subcategory of `k`-algebras whose
objects are one-dimensional function fields over `k`.

## Main definition

* `Hartshorne.ProjectiveNonsingularCurveCat`
-/

namespace Hartshorne

open CategoryTheory TopologicalSpace

universe u

variable (k : Type u) [Field k]

/-- A quasi-projective curve with a specified finite projective presentation.

The ambient space is `P^ambient`; its homogeneous coordinates are consequently
indexed by `Fin (ambient + 1)`. -/
structure QuasiProjectiveCurveCat where
  /-- The dimension of the ambient projective space. -/
  ambient : ℕ
  /-- The presented subset of the ambient projective space. -/
  carrier : Set (ProjectiveSpace k (Fin (ambient + 1)))
  /-- The presentation is quasi-projective. -/
  isQuasiProjective : IsQuasiProjVariety carrier
  /-- The presented variety has dimension one. -/
  isCurve : (Variety.ofQuasiProjective isQuasiProjective).IsCurve

namespace QuasiProjectiveCurveCat

variable {k}

/-- The variety represented by a quasi-projective curve object. -/
noncomputable def toVariety (X : QuasiProjectiveCurveCat k) : Variety k :=
  Variety.ofQuasiProjective X.isQuasiProjective

/-- The represented variety is separated. -/
theorem isSeparated (X : QuasiProjectiveCurveCat k) : X.toVariety.IsSeparated :=
  isSeparated_ofQuasiProjective X.isQuasiProjective

/-- Quasi-projective curves and dominant rational maps form a category. -/
noncomputable instance : Category (QuasiProjectiveCurveCat k) where
  Hom X Y := DominantRatMap X.toVariety Y.toVariety Y.isSeparated
  id X := DominantRatMap.id X.toVariety X.isSeparated
  comp f g := DominantRatMap.comp g f
  id_comp := fun {X _} f => DominantRatMap.comp_id (hX := X.isSeparated) f
  comp_id := fun {_ _} f => DominantRatMap.id_comp f
  assoc := fun {_ _ _ _} f g h => (DominantRatMap.assoc f g h).symm

@[simp]
theorem id_def (X : QuasiProjectiveCurveCat k) :
    (𝟙 X : X ⟶ X) = DominantRatMap.id X.toVariety X.isSeparated :=
  rfl

@[simp]
theorem comp_def {X Y Z : QuasiProjectiveCurveCat k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = DominantRatMap.comp g f :=
  rfl

end QuasiProjectiveCurveCat

/-- A nonsingular projective curve with a specified finite projective
presentation.  Morphisms in its category are dominant morphisms of the
represented varieties. -/
structure ProjectiveNonsingularCurveCat where
  /-- The dimension of the ambient projective space. -/
  ambient : ℕ
  /-- The presented subset of the ambient projective space. -/
  carrier : Set (ProjectiveSpace k (Fin (ambient + 1)))
  /-- The presentation is projective. -/
  isProjective : IsProjVariety carrier
  /-- The presented variety has dimension one. -/
  isCurve : (Variety.ofProjective isProjective).IsCurve
  /-- The presented curve is nonsingular. -/
  isNonsingular : (Variety.ofProjective isProjective).Nonsingular

namespace ProjectiveNonsingularCurveCat

variable {k}

/-- The variety represented by a nonsingular projective curve object. -/
noncomputable def toVariety (X : ProjectiveNonsingularCurveCat k) : Variety k :=
  Variety.ofProjective X.isProjective

/-- A morphism between projective-curve objects, bundled with its dominance. -/
abbrev Hom (X Y : ProjectiveNonsingularCurveCat k) :=
  {f : VarietyHom X.toVariety Y.toVariety // DenseRange f.toFun}

/-- Nonsingular projective curves and dominant morphisms form a category. -/
noncomputable instance : Category (ProjectiveNonsingularCurveCat k) where
  Hom := Hom
  id X := ⟨VarietyHom.id X.toVariety, Function.Surjective.denseRange Function.surjective_id⟩
  comp f g :=
    ⟨g.1.comp f.1, by
      change DenseRange (g.1.toFun ∘ f.1.toFun)
      exact DenseRange.comp g.2 f.2 g.1.continuous_toFun⟩
  id_comp := fun f => Subtype.ext (VarietyHom.comp_id f.1)
  comp_id := fun f => Subtype.ext (VarietyHom.id_comp f.1)
  assoc := fun f g h => Subtype.ext (VarietyHom.comp_assoc h.1 g.1 f.1)

@[simp]
theorem id_val (X : ProjectiveNonsingularCurveCat k) :
    (𝟙 X : X ⟶ X).1 = VarietyHom.id X.toVariety :=
  rfl

@[simp]
theorem comp_val {X Y Z : ProjectiveNonsingularCurveCat k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = g.1.comp f.1 :=
  rfl

end ProjectiveNonsingularCurveCat

/-- The property of being a one-dimensional function field over `k`. -/
def IsOneDimensionalFunctionField : ObjectProperty (CommAlgCat.{u} k) :=
  fun K => IsField K ∧ Algebra.EssFiniteType k K ∧ Algebra.trdeg k K = 1

/-- One-dimensional function fields over `k`, with `k`-algebra homomorphisms. -/
abbrev OneDimensionalFunctionFieldCat :=
  (IsOneDimensionalFunctionField k).FullSubcategory

end Hartshorne
