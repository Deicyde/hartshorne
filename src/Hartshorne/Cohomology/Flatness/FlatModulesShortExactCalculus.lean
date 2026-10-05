/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Flat modules in short exact sequences

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.1A(e) (p. 254).

This file records the two flatness closure rules for a short exact sequence of
modules, expressed directly in terms of its two linear maps.
-/

open TensorProduct

namespace Hartshorne

universe u v w x

/-- **Hartshorne III.9, Proposition 9.1A(e).** For a short exact sequence
`0 → M' → M → M'' → 0`, the middle module is flat when both outside
modules are flat, and the kernel is flat when the middle and quotient modules
are flat. -/
theorem flat_shortExact_calculus
    {R : Type u} [CommRing R]
    {M' : Type w} {M : Type v} {M'' : Type x}
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module R M'] [Module R M] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    (Module.Flat R M' ∧ Module.Flat R M'' → Module.Flat R M) ∧
      (Module.Flat R M ∧ Module.Flat R M'' → Module.Flat R M') := by
  constructor
  · rintro ⟨hM', hM''⟩
    let _ : Module.Flat R M' := hM'
    let _ : Module.Flat R M'' := hM''
    rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
    intro N N' _ _ _ _ l hl
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hgz : g.lTensor N z = 0 := by
      apply Module.Flat.rTensor_preserves_injective_linearMap (M := M'') l hl
      calc
        l.rTensor M'' (g.lTensor N z) = g.lTensor N' (l.rTensor M z) := by
          simp only [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
            LinearMap.lTensor_comp_rTensor]
        _ = 0 := by rw [hz, map_zero]
    obtain ⟨y, hy⟩ := (lTensor_exact N hfg hg z).mp hgz
    have hy0 : l.rTensor M' y = 0 := by
      apply LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg N'
      calc
        f.lTensor N' (l.rTensor M' y) = l.rTensor M (f.lTensor N y) := by
          simp only [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
            LinearMap.rTensor_comp_lTensor]
        _ = 0 := by rw [hy, hz]
        _ = f.lTensor N' 0 := by rw [map_zero]
    have hy' : y = 0 := by
      apply Module.Flat.rTensor_preserves_injective_linearMap (M := M') l hl
      simpa using hy0
    rw [← hy, hy', map_zero]
  · rintro ⟨hM, hM''⟩
    let _ : Module.Flat R M := hM
    let _ : Module.Flat R M'' := hM''
    rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
    intro N N' _ _ _ _ l hl
    rw [injective_iff_map_eq_zero]
    intro z hz
    apply LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg N
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M) l hl
    calc
      l.rTensor M (f.lTensor N z) = f.lTensor N' (l.rTensor M' z) := by
        simp only [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
          LinearMap.lTensor_comp_rTensor]
      _ = 0 := by rw [hz, map_zero]

end Hartshorne
