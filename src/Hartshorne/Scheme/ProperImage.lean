/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteType
import Hartshorne.Scheme.ProperMorphismCalculus
import Hartshorne.Scheme.SeparatedMorphismCalculus

/-!
# Images of proper schemes

Hartshorne, *Algebraic Geometry*, II.4, Exercise 4.4 (p. 106).

The image in a separated finite-type `S`-scheme of a closed subscheme proper over `S` is closed,
and its scheme-theoretic image remains proper over `S`.
-/

open CategoryTheory

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- **Hartshorne II.4, Exercise 4.4.** Let `X` and `Y` be separated finite-type schemes over a
Noetherian scheme `S`. If `Z ⟶ X` is a closed subscheme proper over `S` and `f : X ⟶ Y` is
an `S`-morphism, then the topological image of `Z` is closed in `Y` and its scheme-theoretic image
is proper over `S`. -/
theorem properImage
    {S X Y Z : Scheme.{u}}
    (pX : X ⟶ S) (pY : Y ⟶ S) (i : Z ⟶ X) (f : X ⟶ Y)
    [IsNoetherian S] [IsSeparated pX] [IsSeparated pY]
    (hXft : FiniteType pX) (hYft : FiniteType pY)
    [IsClosedImmersion i] [IsProper (i ≫ pX)]
    (hf : f ≫ pY = pX) :
    IsClosed (Set.range (i ≫ f)) ∧ IsProper ((i ≫ f).imageι ≫ pY) := by
  let g := i ≫ f
  let _ : LocallyOfFiniteType pX := hXft.1
  let _ : QuasiCompact pX := hXft.2
  let _ : LocallyOfFiniteType pY := hYft.1
  have hgcomp : g ≫ pY = i ≫ pX := by
    simp [g, Category.assoc, hf]
  let _ : IsProper (g ≫ pY) := hgcomp ▸ inferInstance
  let _ : IsProper g := IsProper.of_comp g pY
  constructor
  · exact g.isClosedMap.isClosed_range
  · suffices UniversallyClosed (g.imageι ≫ pY) from ⟨⟩
    have : UniversallyClosed (g.toImage ≫ g.imageι ≫ pY) := by
      rw [Scheme.Hom.toImage_imageι_assoc]
      infer_instance
    exact UniversallyClosed.of_comp_surjective g.toImage _

end Hartshorne
