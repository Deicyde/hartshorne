/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RegularLocalGlobalDimension
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Projectivity over a regular local ring is detected by `Ext` against the ring

Hartshorne, *Algebraic Geometry*, III, Exercise 6.6(a) (p. 238).

Let `A` be a regular local ring and `M` a finitely generated `A`-module. Then `M` is projective
if and only if `Ext^i_A(M, A) = 0` for all `i > 0`.

## Proof

Projective modules have no higher `Ext`. Conversely, `pd_A M ≤ d` for `d` the number of
generators of the maximal ideal, so `Ext^i(M, N) = 0` for all `i > d`. By descending induction on
`i ≥ 1`, `Ext^i(M, N) = 0` for every finitely generated `N`: choose `0 → K → A^r → N → 0` with `K`
finitely generated; in the exact sequence `Ext^i(M, A^r) → Ext^i(M, N) → Ext^{i+1}(M, K)` the
outer terms vanish, the first because `Ext^i(M, A^r) = Ext^i(M, A)^r`. For `i = 1` this makes `M`
projective (`ModuleCat.hasProjectiveDimensionLT_of_forall_finite`).

## Main result

* `Hartshorne.RegularLocal.projective_iff_forall_subsingleton_ext`
-/

universe u

open CategoryTheory Abelian IsLocalRing Limits

namespace Hartshorne.RegularLocal

variable {R : Type u} [CommRing R]

/-- `Ext` into isomorphic objects: subsingleton-ness transfers along an isomorphism. -/
lemma subsingleton_ext_of_iso_right (M : ModuleCat.{u} R) {Y Y' : ModuleCat.{u} R} (e : Y ≅ Y')
    (n : ℕ) [Subsingleton (Ext M Y' n)] : Subsingleton (Ext M Y n) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : Ext M Y n,
      z = (z.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ e.inv) (add_zero n) := by
    intro z
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.comp_mk₀_id]
  rw [key x, key y, Subsingleton.elim (x.comp (Ext.mk₀ e.hom) (add_zero n))
    (y.comp (Ext.mk₀ e.hom) (add_zero n))]

/-- If `Ext^n(M, R) = 0`, then `Ext^n(M, R^r) = 0`. -/
lemma subsingleton_ext_pi (M : ModuleCat.{u} R) (r n : ℕ)
    [Subsingleton (Ext M (ModuleCat.of R R) n)] :
    Subsingleton (Ext M (ModuleCat.of R (Fin r → R)) n) := by
  have : Subsingleton (Ext M (⨁ fun _ : Fin r => ModuleCat.of R R) n) :=
    (Ext.addEquivBiproduct M (biproduct.isBilimit _) n).toEquiv.subsingleton_congr.mpr
      inferInstance
  exact subsingleton_ext_of_iso_right M
    (ModuleCat.biproductIsoPi (fun _ : Fin r => ModuleCat.of R R)).symm n

/-- **Hartshorne III, Exercise 6.6(a).** Over a regular local ring `R`, a finitely generated
module `M` is projective if and only if `Ext^i_R(M, R) = 0` for every `i > 0`. -/
theorem projective_iff_forall_subsingleton_ext [IsRegularLocalRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    Projective M ↔ ∀ i, 0 < i → Subsingleton (Ext M (ModuleCat.of R R) i) := by
  refine ⟨fun _ i hi => ?_, fun h => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact Ext.subsingleton_of_projective M _ j
  set d := (maximalIdeal R).spanFinrank
  have hpd : HasProjectiveDimensionLT M (d + 1) :=
    hasProjectiveDimensionLE_of_isRegularLocalRing R M
  have key : ∀ k i : ℕ, 0 < i → d + 1 ≤ i + k → ∀ L : ModuleCat.{u} R, Module.Finite R L →
      Subsingleton (Ext M L i) := by
    intro k
    induction k with
    | zero =>
      intro i _ hi L _
      exact HasProjectiveDimensionLT.subsingleton M (d + 1) i (by omega) L
    | succ k ih =>
      intro i hi hik L _
      obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R L
      let S : ShortComplex (ModuleCat.{u} R) :=
        ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker π).subtype) (ModuleCat.ofHom π)
          (by ext x; exact x.2)
      have hS : S.ShortExact :=
        { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
            (LinearMap.exact_subtype_ker_map π)
          mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker π).injective_subtype
          epi_g := (ModuleCat.epi_iff_surjective _).mpr hπ }
      have h₁ : Subsingleton (Ext M S.X₁ (i + 1)) :=
        ih (i + 1) (by omega) (by omega) S.X₁ (inferInstanceAs (Module.Finite R (LinearMap.ker π)))
      have : Subsingleton (Ext M (ModuleCat.of R R) i) := h i hi
      have h₂ : Subsingleton (Ext M S.X₂ i) := subsingleton_ext_pi M r i
      refine ⟨fun x y => ?_⟩
      suffices hz : ∀ z : Ext M S.X₃ i, z = 0 by rw [hz x, hz y]
      intro z
      obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ M hS z rfl (Subsingleton.elim _ _)
      rw [← hw, Subsingleton.elim w 0, Ext.zero_comp]
  have h1 : HasProjectiveDimensionLT M 1 :=
    ModuleCat.hasProjectiveDimensionLT_of_forall_finite M 1
      fun L _ => key d 1 one_pos (by omega) L ‹_›
  exact projective_iff_hasProjectiveDimensionLT_one.mpr h1

end Hartshorne.RegularLocal
