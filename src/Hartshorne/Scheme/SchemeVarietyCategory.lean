/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.AffineOpenBasis
import Mathlib.CategoryTheory.Category.Basic

/-!
# The scheme-variety source category

The source category for Hartshorne, *Algebraic Geometry*, Proposition II.2.6.
Its objects are the project's varieties equipped with the affine-open-basis
witness needed to construct their associated schemes, and its morphisms are
the existing `VarietyHom`s.
-/

namespace Hartshorne

open CategoryTheory

universe u

/-- A variety equipped with an affine-open basis. This is the source category
for the comparison between classical varieties and schemes. -/
@[ext]
structure SchemeVarietyCat (k : Type u) [Field k] where
  /-- The underlying project variety. -/
  toVariety : Variety.{u, u} k
  /-- Every neighbourhood in the underlying variety contains an affine open
  neighbourhood. -/
  hasAffineOpenBasis : toVariety.HasAffineOpenBasis

namespace SchemeVarietyCat

variable {k : Type u} [Field k]

/-- Morphisms in the scheme-variety source category are morphisms of the
underlying varieties. -/
abbrev Hom (X Y : SchemeVarietyCat k) :=
  VarietyHom X.toVariety Y.toVariety

/-- Varieties with an affine-open basis and their existing morphisms form a
category. -/
instance : Category.{u} (SchemeVarietyCat k) where
  Hom := Hom
  id X := VarietyHom.id X.toVariety
  comp f g := g.comp f
  id_comp f := VarietyHom.comp_id f
  comp_id f := VarietyHom.id_comp f
  assoc f g h := (VarietyHom.comp_assoc h g f).symm

@[simp]
theorem id_def (X : SchemeVarietyCat k) :
    (𝟙 X : X ⟶ X) = VarietyHom.id X.toVariety :=
  rfl

@[simp]
theorem comp_def {X Y Z : SchemeVarietyCat k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = VarietyHom.comp g f :=
  rfl

end SchemeVarietyCat

end Hartshorne
