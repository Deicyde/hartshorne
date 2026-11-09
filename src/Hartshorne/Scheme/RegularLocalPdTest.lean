/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RegularLocalProjectiveTest

/-!
# Projective dimension over a regular local ring is detected by `Ext` against the ring

Hartshorne, *Algebraic Geometry*, III, Exercise 6.6(b) (p. 238).

Let `A` be a regular local ring and `M` a finitely generated `A`-module. For every `n`,
`pd_A M ≤ n` if and only if `Ext^i_A(M, A) = 0` for all `i > n`.

## Proof

If `pd_A M ≤ n`, all `Ext^i(M, -)` with `i > n` vanish. Conversely, `pd_A M ≤ d` for `d` the
number of generators of the maximal ideal. By descending induction on `i > n`,
`Ext^i(M, N) = 0` for every finitely generated `N`: choose `0 → K → A^r → N → 0` with `K`
finitely generated; in the exact sequence `Ext^i(M, A^r) → Ext^i(M, N) → Ext^{i+1}(M, K)` the
outer terms vanish. For `i = n + 1` this gives `pd_A M ≤ n`
(`ModuleCat.hasProjectiveDimensionLT_of_forall_finite`).

## Main result

* `Hartshorne.RegularLocal.hasProjectiveDimensionLE_iff_forall_subsingleton_ext`
-/

universe u

open CategoryTheory Abelian IsLocalRing Limits

namespace Hartshorne.RegularLocal

variable {R : Type u} [CommRing R]

/-- **Hartshorne III, Exercise 6.6(b).** Over a regular local ring `R`, a finitely generated
module `M` has projective dimension at most `n` if and only if `Ext^i_R(M, R) = 0` for every
`i > n`. -/
theorem hasProjectiveDimensionLE_iff_forall_subsingleton_ext [IsRegularLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    HasProjectiveDimensionLE M n ↔ ∀ i, n < i → Subsingleton (Ext M (ModuleCat.of R R) i) := by
  refine ⟨fun hM i hi => HasProjectiveDimensionLT.subsingleton M (n + 1) i hi _, fun h => ?_⟩
  set d := (maximalIdeal R).spanFinrank
  have hpd : HasProjectiveDimensionLT M (d + 1) :=
    hasProjectiveDimensionLE_of_isRegularLocalRing R M
  have key : ∀ k i : ℕ, n < i → d + 1 ≤ i + k → ∀ L : ModuleCat.{u} R, Module.Finite R L →
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
  exact ModuleCat.hasProjectiveDimensionLT_of_forall_finite M (n + 1)
    fun L _ => key d (n + 1) (by omega) (by omega) L ‹_›

end Hartshorne.RegularLocal
