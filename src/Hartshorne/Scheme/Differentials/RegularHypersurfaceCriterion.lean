/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Regular hypersurface quotients of a regular local ring

Hartshorne, *Algebraic Geometry*, II.8, the local calculation in the proof of
Theorem 8.18 (pp. 179–180).

Let `(A, 𝔪)` be a regular local domain and let `f ∈ 𝔪` be nonzero. Then `A ⧸ (f)` is a
regular local ring if and only if the class of `f` in the cotangent space `𝔪 ⧸ 𝔪²` is nonzero,
equivalently `f ∉ 𝔪²`.

Since `A` is a domain, `f` is a non-zero-divisor, so `dim A ⧸ (f) = dim A - 1`. If `f ∉ 𝔪²`,
the class of `f` extends to a basis of `𝔪 ⧸ 𝔪²`; by Nakayama the lifts of this basis generate
`𝔪`, and dropping `f` leaves `dim A - 1` generators of the maximal ideal of `A ⧸ (f)`. If
`f ∈ 𝔪²`, lifts of any generating set of the maximal ideal of `A ⧸ (f)` generate `𝔪` modulo
`𝔪²`, hence generate `𝔪` by Nakayama, so `A ⧸ (f)` needs at least `dim A` generators.

## Main results

* `Hartshorne.isRegularLocalRing_quotient_span_singleton_iff_notMem_sq`
* `Hartshorne.isRegularLocalRing_quotient_span_singleton_iff_toCotangent_ne_zero`
-/

namespace Hartshorne

open IsLocalRing Ideal

/-- Let `(A, 𝔪)` be a regular local domain and `f ∈ 𝔪` nonzero. Then `A ⧸ (f)` is regular if
and only if `f ∉ 𝔪²`. -/
theorem isRegularLocalRing_quotient_span_singleton_iff_notMem_sq
    {A : Type*} [CommRing A] [IsRegularLocalRing A] [IsDomain A] {f : A}
    (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal A) :
    IsRegularLocalRing (A ⧸ span {f}) ↔ f ∉ maximalIdeal A ^ 2 := by
  set B := A ⧸ span {f}
  let π : A →+* B := Ideal.Quotient.mk (span {f})
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hfB : span {f} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal f).mp hfm
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hfB
  have : IsLocalRing B := IsLocalRing.of_surjective' π hπ
  have hcomap : (maximalIdeal B).comap π = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective π hπ)
  have hmap : (maximalIdeal A).map π = maximalIdeal B := by
    rw [← hcomap, Ideal.map_comap_of_surjective π hπ]
  -- Dimensions: `dim A = n` and `dim B + 1 = n`, where `n` is the number of generators of `𝔪`.
  set n := (maximalIdeal A).spanFinrank
  have hA : (n : WithBot ℕ∞) = ringKrullDim A := (isRegularLocalRing_iff A).mp ‹_›
  have hdim : ringKrullDim B + 1 = ringKrullDim A :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hf0) hfm
  obtain ⟨d, hd, hdn⟩ : ∃ d : ℕ, ringKrullDim B = d ∧ d + 1 = n := by
    rw [← hA] at hdim
    generalize ringKrullDim B = e at hdim ⊢
    induction e using WithBot.recBotCoe with
    | bot => simp at hdim
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add] at hdim
        exact absurd (WithBot.coe_injective hdim) (ENat.top_ne_natCast n)
      | coe e => exact ⟨e, rfl, by exact_mod_cast hdim⟩
  constructor
  · -- If `A ⧸ (f)` is regular, then `f ∉ 𝔪²`.
    intro hB hfsq
    have hBn : (maximalIdeal B).spanFinrank = d := by
      have := (isRegularLocalRing_iff B).mp hB
      rw [hd] at this
      exact_mod_cast this
    have fgB : (maximalIdeal B).FG := (maximalIdeal B).fg_of_isNoetherianRing
    set S := (maximalIdeal B).generators
    have hSfin : S.Finite := Submodule.FG.finite_generators fgB
    set T : Set A := Function.surjInv hπ '' S
    have hTfin : T.Finite := hSfin.image _
    have hπT : π '' T = S := by
      simp only [T, ← Set.image_comp, Function.comp_def, Function.surjInv_eq hπ, Set.image_id']
    have hspan : maximalIdeal A = span T ⊔ span {f} := by
      rw [← hcomap, ← (maximalIdeal B).span_generators]
      change comap π (Submodule.span B S) = _
      rw [← hπT, ← Ideal.span, ← Ideal.map_span, Ideal.comap_map_of_surjective' π hπ,
        Ideal.mk_ker]
    -- Nakayama: since `f ∈ 𝔪²`, the lifts `T` alone generate `𝔪`.
    have hle : maximalIdeal A ≤ span T := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
        (maximalIdeal A).fg_of_isNoetherianRing (maximalIdeal_le_jacobson ⊥) ?_
      rw [smul_eq_mul, ← pow_two]
      conv_lhs => rw [hspan]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hfsq) _
    have hT : maximalIdeal A = span T :=
      le_antisymm hle (Ideal.span_le.mpr fun x hx ↦ hspan ▸ Ideal.mem_sup_left (subset_span hx))
    have : n ≤ d := by
      rw [show n = (maximalIdeal A).spanFinrank from rfl, hT, ← hBn]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite hTfin).trans ?_
      rw [← Submodule.FG.generators_ncard fgB]
      exact Set.ncard_image_le hSfin
    omega
  · -- If `f ∉ 𝔪²`, extend the class of `f` to a basis of `𝔪 ⧸ 𝔪²`.
    intro hfsq
    set k := ResidueField A
    set V := CotangentSpace A
    set v : V := (maximalIdeal A).toCotangent ⟨f, hfm⟩
    have hv : v ≠ 0 := by
      rwa [Ne, Ideal.toCotangent_eq_zero]
    have hs : LinearIndepOn k id ({v} : Set V) := LinearIndepOn.singleton hv
    set E := hs.extend (Set.subset_univ _)
    let b : Module.Basis E k V := Module.Basis.extend hs
    have hvE : v ∈ E := hs.subset_extend _ (Set.mem_singleton v)
    have hEspan : Submodule.span k E = ⊤ := by
      have := b.span_eq
      rwa [Module.Basis.range_extend] at this
    have : Module.Finite k V := inferInstance
    have hEfin : E.Finite := Set.toFinite E
    have hEcard : E.ncard = n := by
      rw [← Nat.card_coe_set_eq, ← Module.finrank_eq_nat_card_basis b,
        ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    -- Lift the remaining basis vectors to `𝔪`.
    obtain ⟨g, hg⟩ : ∃ g : V → maximalIdeal A, ∀ y, (maximalIdeal A).toCotangent (g y) = y :=
      ⟨_, Function.surjInv_eq (maximalIdeal A).toCotangent_surjective⟩
    set s : Set (maximalIdeal A) := insert ⟨f, hfm⟩ (g '' (E \ {v}))
    have himg : (maximalIdeal A).toCotangent '' s = E := by
      simp only [s, Set.image_insert_eq, ← Set.image_comp, Function.comp_def, hg,
        Set.image_id']
      exact Set.insert_sdiff_singleton.trans (Set.insert_eq_of_mem hvE)
    have hsA : Submodule.span A s = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, himg, hEspan]
    set U : Set A := (fun x : V ↦ (g x : A)) '' (E \ {v})
    have hUfin : U.Finite := (hEfin.sdiff).image _
    have hmA : maximalIdeal A = span (insert f U) := by
      have := congrArg (Submodule.map (maximalIdeal A).subtype) hsA
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
      rw [← this]
      simp only [s, U, Set.image_insert_eq, ← Set.image_comp, Function.comp_def,
        Submodule.subtype_apply]
    have hmB : maximalIdeal B = span (π '' U) := by
      rw [← hmap, hmA, Ideal.map_span, Set.image_insert_eq,
        show π f = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self f),
        Ideal.span_insert_zero]
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [hd, hmB]
    have h1 : (span (π '' U)).spanFinrank ≤ (E \ {v}).ncard :=
      (Submodule.spanFinrank_span_le_ncard_of_finite (hUfin.image _)).trans
        ((Set.ncard_image_le hUfin).trans (Set.ncard_image_le hEfin.sdiff))
    have h2 : (E \ {v}).ncard + 1 = n := by
      rw [Set.ncard_sdiff_singleton_add_one hvE hEfin, hEcard]
    exact_mod_cast (show (span (π '' U)).spanFinrank ≤ d by omega)

/-- Let `(A, 𝔪)` be a regular local domain and `f ∈ 𝔪` nonzero. Then `A ⧸ (f)` is regular if
and only if the class of `f` in `𝔪 ⧸ 𝔪²` is nonzero. -/
theorem isRegularLocalRing_quotient_span_singleton_iff_toCotangent_ne_zero
    {A : Type*} [CommRing A] [IsRegularLocalRing A] [IsDomain A] {f : A}
    (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal A) :
    IsRegularLocalRing (A ⧸ span {f}) ↔ (maximalIdeal A).toCotangent ⟨f, hfm⟩ ≠ 0 := by
  rw [isRegularLocalRing_quotient_span_singleton_iff_notMem_sq hf0 hfm, Ne,
    Ideal.toCotangent_eq_zero]

end Hartshorne
