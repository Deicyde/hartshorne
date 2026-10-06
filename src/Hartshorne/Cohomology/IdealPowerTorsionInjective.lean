/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ArtinReesInducedTopology
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-!
# Ideal-power torsion in an injective module

Hartshorne, *Algebraic Geometry*, III, Lemma 3.2, pp. 213--214.

Over a Noetherian ring, the submodule of ideal-power torsion elements in an
injective module is injective. The proof combines Baer's criterion with the
Artin--Rees theorem.
-/

noncomputable section

universe u

namespace Hartshorne

private lemma exists_pow_smul_top_le_ker
    {A E : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup E] [Module A E]
    (a J : Ideal A) (φ : J →ₗ[A] Ideal.primaryComponent E a) :
    ∃ n : ℕ, a ^ n • (⊤ : Submodule A J) ≤
      LinearMap.ker ((Ideal.primaryComponent E a).subtype.comp φ) := by
  let _ : Module.Finite A J :=
    Module.Finite.of_fg (Ideal.fg_of_isNoetherianRing J)
  obtain ⟨d, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := J)
  choose e he using fun i ↦
    (Ideal.primaryComponent_mem E a (φ (s i)).1).mp (φ (s i)).2
  let n := Finset.univ.sup e
  have hφ : (⊤ : Submodule A J) ≤
      (Submodule.torsionBySet A E ↑(a ^ n)).comap
        ((Ideal.primaryComponent E a).subtype.comp φ) := by
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.torsionBySet_le_torsionBySet_pow
      (e i) n (Finset.le_sup (Finset.mem_univ i)) a (he i)
  refine ⟨n, fun x hx ↦ ?_⟩
  rw [LinearMap.mem_ker]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [map_smul]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hφ trivial) ⟨r, hr⟩
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- If `E` is an injective module over a Noetherian ring, then its submodule
of elements annihilated by some power of `a` is injective. -/
theorem idealPowerTorsion_injective
    {A E : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup E] [Module A E]
    (a : Ideal A) (hE : Module.Injective A E) :
    Module.Injective A (Ideal.primaryComponent E a) := by
  apply Module.Baer.injective
  intro J φ
  let ψ : J →ₗ[A] E := (Ideal.primaryComponent E a).subtype.comp φ
  obtain ⟨n, hn⟩ := exists_pow_smul_top_le_ker a J φ
  obtain ⟨k, _, hk⟩ := artinRees_inducedTopology a J n
  let p : A →ₗ.[A] E := ⟨J, ψ⟩
  let z : A →ₗ.[A] E := ⟨a ^ k • (⊤ : Submodule A A), 0⟩
  have hpz : ∀ (x : p.domain) (y : z.domain), (x : A) = y → p x = z y := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    change ψ ⟨x, hx⟩ = 0
    apply LinearMap.mem_ker.mp
    apply hn
    apply (Submodule.mem_smul_top_iff (I := a ^ n) J ⟨x, hx⟩).mpr
    apply hk
    exact ⟨hx, hxy ▸ hy⟩
  let q : A →ₗ.[A] E := p.sup z hpz
  have hEBaer : Module.Baer A E := Module.Baer.iff_injective.mpr hE
  obtain ⟨g, hg⟩ := hEBaer q.domain q.toFun
  have hzq : z ≤ q := LinearPMap.right_le_sup p z hpz
  have hpq : p ≤ q := LinearPMap.left_le_sup p z hpz
  have hg_zero {x : A} (hx : x ∈ z.domain) : g x = 0 := by
    calc
      g x = q ⟨x, hzq.1 hx⟩ := hg x (hzq.1 hx)
      _ = z ⟨x, hx⟩ := (hzq.2 rfl).symm
      _ = 0 := rfl
  have hg_mem (x : A) : g x ∈ Ideal.primaryComponent E a := by
    apply (Ideal.primaryComponent_mem E a (g x)).mpr
    refine ⟨k, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨r, hr⟩
    rw [← g.map_smul]
    exact hg_zero (Submodule.smul_mem_smul hr trivial)
  let g' : A →ₗ[A] Ideal.primaryComponent E a :=
    g.codRestrict (Ideal.primaryComponent E a) hg_mem
  refine ⟨g', fun x hx ↦ ?_⟩
  apply Subtype.ext
  calc
    g x = q ⟨x, hpq.1 hx⟩ := hg x (hpq.1 hx)
    _ = p ⟨x, hx⟩ := (hpq.2 rfl).symm
    _ = φ ⟨x, hx⟩ := rfl

end Hartshorne
