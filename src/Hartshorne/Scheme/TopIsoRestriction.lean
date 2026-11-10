/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restriction along `X ≅ ⊤`

Two small lemmas about transporting sections along the isomorphism `X.topIso : ⊤ ≅ X` between
a scheme and its top open subscheme, shared by the projective-variety and Euler-sequence
material.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Hartshorne

/-- Restricting a section over an open `U ⊇ ⊤` to the image of `⊤` and then
transporting it along `X ≅ ⊤` is restriction to `⊤`. -/
theorem topIso_inv_appTop_presheaf_map {X : Scheme.{u}} {U : X.Opens} (h : ⊤ ≤ U)
    (φ : op U ⟶ op ((⊤ : X.Opens).ι ''ᵁ ⊤)) (a : Γ(X, U)) :
    X.topIso.inv.appTop (X.presheaf.map φ a) = X.presheaf.map (homOfLE h).op a := by
  have hφ : φ = (homOfLE h).op ≫ (homOfLE (x := (⊤ : X.Opens).ι ''ᵁ ⊤) le_top).op := rfl
  have key : (Scheme.Opens.ι ⊤).appTop ≫ X.topIso.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Scheme.toIso_inv_ι, Scheme.Hom.id_appTop]
  rw [hφ, Functor.map_comp, CommRingCat.comp_apply, ← Scheme.Opens.ι_appTop]
  change ((Scheme.Opens.ι ⊤).appTop ≫ X.topIso.inv.appTop) _ = _
  rw [key]
  rfl

/-- A variant of `topIso_inv_appTop_presheaf_map` through an intermediate open `V`. -/
theorem topIso_inv_appTop_presheaf_map_map {X : Scheme.{u}} {U V : X.Opens} (h : ⊤ ≤ U)
    (ψ : op U ⟶ op V) (φ : op V ⟶ op ((⊤ : X.Opens).ι ''ᵁ ⊤)) (a : Γ(X, U)) :
    X.topIso.inv.appTop (X.presheaf.map φ (X.presheaf.map ψ a)) =
      X.presheaf.map (homOfLE h).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  exact topIso_inv_appTop_presheaf_map h _ a

end Hartshorne
