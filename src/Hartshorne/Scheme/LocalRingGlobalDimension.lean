/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# The residue field controls projective dimension over a Noetherian local ring

Let `R` be a Noetherian local ring with residue field `k`. If `k` has projective dimension at
most `n`, then every finitely generated `R`-module has projective dimension at most `n`
(Matsumura, *Commutative Ring Theory*, Theorem 19.1 and Lemma 19.1; Stacks, tag 00O3 and
tag 00O5).

The proof only uses `Ext`:

* `Ext`-vanishing in degrees `> n` against a fixed module passes to every finitely generated
  module once it holds for all quotients `R ⧸ 𝔭` by primes, by a prime filtration;
* for a prime `𝔮 ≠ 𝔪` and `x ∈ 𝔪 \ 𝔮`, the sequence `0 → R/𝔮 → R/𝔮 → R/(𝔮 + x) → 0` and
  Nakayama's lemma on the finitely generated module `Ext^i(R/𝔮, L)` reduce vanishing for `R ⧸ 𝔮`
  to vanishing for primes strictly containing `𝔮`; at `𝔮 = 𝔪` it is the hypothesis on `k`;
* `ModuleCat.hasProjectiveDimensionLT_of_forall_finite` turns vanishing of `Ext^{n+1}(M, L)` for
  all finitely generated `L` into the projective dimension bound.
-/

universe u

open CategoryTheory Abelian IsLocalRing

namespace Hartshorne.LocalGlobalDimension

variable {R : Type u} [CommRing R]

/-- `Ext` out of isomorphic objects: subsingleton-ness transfers along an isomorphism. -/
lemma subsingleton_ext_of_iso {A B : ModuleCat.{u} R} (e : A ≅ B) (L : ModuleCat.{u} R) (i : ℕ)
    [Subsingleton (Ext B L i)] : Subsingleton (Ext A L i) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : Ext A L i,
      z = (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp z (zero_add i)) (zero_add i) := by
    intro z
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.mk₀_id_comp]
  rw [key x, key y, Subsingleton.elim ((Ext.mk₀ e.inv).comp x (zero_add i))
    ((Ext.mk₀ e.inv).comp y (zero_add i))]

/-- Vanishing of `Ext^i(-, L)` in degrees `i > n` passes from the quotients `R ⧸ 𝔭` by primes
containing an ideal `I` to every finitely generated module killed by `I`. -/
theorem subsingleton_ext_of_forall_prime [IsNoetherianRing R] (L : ModuleCat.{u} R) (n : ℕ)
    (I : Ideal R)
    (hP : ∀ p : Ideal R, p.IsPrime → I ≤ p → ∀ i, n < i →
      Subsingleton (Ext (ModuleCat.of R (R ⧸ p)) L i))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I ≤ Module.annihilator R M) (i : ℕ) (hi : n < i) :
    Subsingleton (Ext (ModuleCat.of R M) L i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  revert hI
  induction ‹Module.Finite R M› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
    intro _
    have : Projective (ModuleCat.of R N) :=
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R N)).projective
    exact Ext.subsingleton_of_projective _ _ _
  | quotient N p e =>
    intro hI
    have hp : I ≤ p.1 := by
      intro r hr
      have hr' := hI hr
      rw [Module.mem_annihilator] at hr'
      have h1 : r • e.symm (Ideal.Quotient.mk p.1 1) = 0 := hr' _
      rw [← map_smul, LinearEquiv.map_eq_zero_iff, Algebra.smul_def, map_one, mul_one,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact h1
    have := hP p.1 p.2 hp (j + 1) hi
    exact subsingleton_ext_of_iso e.toModuleIso L (j + 1)
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hI
    have hI₁ : I ≤ Module.annihilator R N₁ := fun r hr => by
      have hr := hI hr
      rw [Module.mem_annihilator] at hr ⊢
      intro m
      apply hf
      rw [map_smul, hr, map_zero]
    have hI₃ : I ≤ Module.annihilator R N₃ := fun r hr => by
      have hr := hI hr
      rw [Module.mem_annihilator] at hr ⊢
      intro m
      obtain ⟨m, rfl⟩ := hg m
      rw [← map_smul, hr, map_zero]
    have s₁ := h₁ hI₁
    have s₃ := h₃ hI₃
    let S : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (by ext x; exact hfg.apply_apply_eq_zero x)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr hfg
        mono_f := (ModuleCat.mono_iff_injective _).mpr hf
        epi_g := (ModuleCat.epi_iff_surjective _).mpr hg }
    refine ⟨fun x y => ?_⟩
    suffices h : ∀ z : Ext S.X₂ L (j + 1), z = 0 by rw [h x, h y]
    intro z
    have hz : (Ext.mk₀ S.f).comp z (zero_add (j + 1)) = 0 := Subsingleton.elim _ _
    obtain ⟨w, hw⟩ := Ext.contravariant_sequence_exact₂ hS L z hz
    rw [← hw, Subsingleton.elim w 0, Ext.comp_zero]

/-- An element outside a prime `𝔮` is a non-zero-divisor on `R ⧸ 𝔮`. -/
lemma isSMulRegular_quotient_of_notMem {q : Ideal R} [q.IsPrime] {x : R} (hx : x ∉ q) :
    IsSMulRegular (R ⧸ q) x := by
  refine IsSMulRegular.of_right_eq_zero_of_smul (fun m hm => ?_)
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at hm
  refine (mul_eq_zero.mp hm).resolve_left ?_
  exact fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h)

set_option backward.isDefEq.respectTransparency false in
/-- Let `R` be a Noetherian local ring with residue field `k` and `L` a finitely generated
module. If `Ext^i(k, L) = 0` for all `i > n`, then `Ext^i(R ⧸ 𝔮, L) = 0` for every prime `𝔮` and
all `i > n`. -/
theorem subsingleton_ext_quotient_prime [IsLocalRing R] [IsNoetherianRing R]
    (L : ModuleCat.{u} R) [Module.Finite R L] (n : ℕ)
    (hk : ∀ i, n < i → Subsingleton (Ext (ModuleCat.of R (ResidueField R)) L i))
    (q : Ideal R) (hq : q.IsPrime) (i : ℕ) (hi : n < i) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ q)) L i) := by
  induction q using WellFoundedGT.induction generalizing i with
  | _ q ih =>
  by_cases hqm : q = maximalIdeal R
  · subst hqm
    exact hk i hi
  obtain ⟨x, hxm, hxq⟩ : ∃ x ∈ maximalIdeal R, x ∉ q := by
    by_contra! h
    exact hqm (le_antisymm (le_maximalIdeal hq.ne_top) h)
  let M := ModuleCat.of R (R ⧸ q)
  have reg : IsSMulRegular M x := isSMulRegular_quotient_of_notMem hxq
  let S := M.smulShortComplex x
  have hS : S.ShortExact := reg.smulShortComplex_shortExact
  have h3 : Subsingleton (Ext S.X₃ L (i + 1)) := by
    refine subsingleton_ext_of_forall_prime L n (Module.annihilator R (QuotSMulTop x M)) ?_
      (QuotSMulTop x M) le_rfl (i + 1) (by omega)
    intro p hp hle j hj
    refine ih p ?_ hp j hj
    have hxp : x ∈ p := hle (QuotSMulTop.mem_annihilator M x)
    have hqp : q ≤ p := by
      intro r hr
      apply hle
      rw [Module.mem_annihilator]
      intro m
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
      rw [← map_smul]
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      have : r • (Ideal.Quotient.mk q m : R ⧸ q) = 0 := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
          Ideal.Quotient.eq_zero_iff_mem]
        exact q.mul_mem_right m hr
      exact (congrArg _ this).trans (map_zero _)
    exact lt_of_le_of_ne hqp (fun h => hxq (h ▸ hxp))
  have exac := Ext.contravariant_sequence_exact₁' hS L i (i + 1) (add_comm 1 i)
  have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ h3).eq_zero_of_tgt _)
  have : S.f = x • 𝟙 M := rfl
  simp only [S, this, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom] at epi
  by_contra! ntr
  have : x ∈ (Module.annihilator R (Ext M L i)).jacobson :=
    (IsLocalRing.maximalIdeal_le_jacobson _) hxm
  absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
  rw [eq_comm, eq_top_iff]
  intro y _
  rcases epi y with ⟨z, hz⟩
  simp only [ModuleCat.smulShortComplex, Ext.mk₀_smul,
    Ext.bilinearComp_apply_apply, Ext.smul_comp, Ext.mk₀_id_comp] at hz
  simpa [← hz] using Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial

/-- **Matsumura, Lemma 19.1 / Theorem 19.1 (one direction)**: over a Noetherian local ring
whose residue field has projective dimension at most `n`, every finitely generated module has
projective dimension at most `n`. -/
theorem hasProjectiveDimensionLE_of_residueField [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (hk : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n)
    (M : ModuleCat.{u} R) [Module.Finite R M] : HasProjectiveDimensionLE M n := by
  apply ModuleCat.hasProjectiveDimensionLT_of_forall_finite M (n + 1)
  intro L _
  refine subsingleton_ext_of_forall_prime L n ⊥ ?_ M bot_le (n + 1) (by omega)
  intro p hp _ i hi
  exact subsingleton_ext_quotient_prime L n
    (fun i hi => HasProjectiveDimensionLT.subsingleton _ (n + 1) i hi L) p hp i hi

end Hartshorne.LocalGlobalDimension
