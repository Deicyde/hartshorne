/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.RegularFunction
import Hartshorne.Projective.VanishingIdeal

/-!
# Regular functions on a quasi-projective variety

Hartshorne, *Algebraic Geometry*, I.3, the definition on p. 15.

The definition copies the quasi-affine one with two changes: the numerator and
denominator are homogeneous, and they have **the same degree**.

Equal degrees is not bookkeeping. Neither `g` nor `h` is a function on `ℙⁿ`, but
their ratio is, because rescaling the representative multiplies both by the same
`aⁿ` and the ratio is unchanged. Drop the condition and the definition is not
merely weaker, it is meaningless: the value would depend on the representative.

As in the affine case, regularity is parametrised by a map `ι` into projective
space rather than fixed to a subtype inclusion, so that open subsets of subsets
are handled without transporting anything.

## Main definitions

* `Hartshorne.IsRegularProjVia`, `Hartshorne.IsRegularProj`

## Main results

* `Hartshorne.ratio_eq_of_smul` : the ratio is independent of the
  representative. This is what equal degrees buys.
* `Hartshorne.isClosed_eqLocusProjVia` : Lemma 3.1's content, projective case.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}
variable {A : Type*} [TopologicalSpace A] {ι : A → ProjectiveSpace k σ}

/-- The ratio of two homogeneous polynomials **of the same degree** is unchanged
by rescaling, which is exactly why it defines a function on projective space. -/
theorem ratio_eq_of_smul {n : ℕ} {g h : MvPolynomial σ k}
    (hg : g.IsHomogeneous n) (hh : h.IsHomogeneous n) {a : k} (ha : a ≠ 0)
    (v : σ → k) :
    eval (a • v) g / eval (a • v) h = eval v g / eval v h := by
  rw [hg.eval_smul, hh.eval_smul, mul_div_mul_left _ _ (pow_ne_zero n ha)]

/-- `f` is *regular at* `P`, relative to a map `ι` into projective space, when
near `P` it is a ratio of homogeneous polynomials of equal degree in the
homogeneous coordinates, with the denominator nowhere zero. -/
def IsRegularAtProjVia (ι : A → ProjectiveSpace k σ) (f : A → k) (P : A) : Prop :=
  ∃ U : Set A, IsOpen U ∧ P ∈ U ∧ ∃ (n : ℕ) (g h : MvPolynomial σ k),
    g.IsHomogeneous n ∧ h.IsHomogeneous n ∧
      (∀ x ∈ U, eval (ι x).rep h ≠ 0) ∧
        ∀ x ∈ U, f x = eval (ι x).rep g / eval (ι x).rep h

/-- `f` is *regular* relative to `ι` when it is regular at every point. -/
def IsRegularProjVia (ι : A → ProjectiveSpace k σ) (f : A → k) : Prop :=
  ∀ P, IsRegularAtProjVia ι f P

/-- Hartshorne's regularity, for a subset of projective space. -/
def IsRegularProj {Y : Set (ProjectiveSpace k σ)} (f : Y → k) : Prop :=
  IsRegularProjVia Subtype.val f

/-- Constants are regular: numerator `C c` and denominator `1`, both homogeneous
of degree zero. -/
theorem isRegularProjVia_const (ι : A → ProjectiveSpace k σ) (c : k) :
    IsRegularProjVia ι (fun _ => c) := fun _ =>
  ⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, C c, 1, isHomogeneous_C _ _,
    isHomogeneous_one σ k, by simp, by simp⟩

/-- Sums of regular functions are regular. The common denominator `h₁h₂` and
numerator `g₁h₂ + g₂h₁` are both homogeneous of degree `n₁ + n₂`, so the
equal-degree condition is preserved. -/
theorem IsRegularProjVia.add {f g : A → k} (hf : IsRegularProjVia ι f)
    (hg : IsRegularProjVia ι g) : IsRegularProjVia ι (f + g) := by
  intro P
  obtain ⟨U₁, hU₁, hP₁, n₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := hf P
  obtain ⟨U₂, hU₂, hP₂, n₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := hg P
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hP₁, hP₂⟩, n₁ + n₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂,
    (hg₁.mul hh₂).add (by simpa [Nat.add_comm] using hg₂.mul hh₁), hh₁.mul hh₂,
    fun x hx => ?_, fun x hx => ?_⟩
  · simpa using mul_ne_zero (hne₁ x hx.1) (hne₂ x hx.2)
  · have e₁ := hne₁ x hx.1
    have e₂ := hne₂ x hx.2
    rw [Pi.add_apply, he₁ x hx.1, he₂ x hx.2]
    simp only [map_add, map_mul]
    field_simp

/-- Products of regular functions are regular. -/
theorem IsRegularProjVia.mul {f g : A → k} (hf : IsRegularProjVia ι f)
    (hg : IsRegularProjVia ι g) : IsRegularProjVia ι (f * g) := by
  intro P
  obtain ⟨U₁, hU₁, hP₁, n₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := hf P
  obtain ⟨U₂, hU₂, hP₂, n₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := hg P
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hP₁, hP₂⟩, n₁ + n₂, g₁ * g₂, h₁ * h₂,
    hg₁.mul hg₂, hh₁.mul hh₂, fun x hx => ?_, fun x hx => ?_⟩
  · simpa using mul_ne_zero (hne₁ x hx.1) (hne₂ x hx.2)
  · have e₁ := hne₁ x hx.1
    have e₂ := hne₂ x hx.2
    rw [Pi.mul_apply, he₁ x hx.1, he₂ x hx.2]
    simp only [map_mul]
    field_simp

/-- A nowhere-zero regular function has a regular inverse: exchange numerator
and denominator, which keeps their degrees equal. -/
theorem IsRegularProjVia.inv {f : A → k} (hf : IsRegularProjVia ι f)
    (hne : ∀ x, f x ≠ 0) : IsRegularProjVia ι f⁻¹ := by
  intro P
  obtain ⟨U, hU, hP, n, g, h, hg, hh, hh0, he⟩ := hf P
  refine ⟨U, hU, hP, n, h, g, hh, hg, fun x hx hgz => hne x ?_, fun x hx => ?_⟩
  · rw [he x hx, hgz, zero_div]
  · rw [Pi.inv_apply, he x hx, inv_div]

/-- **Lemma 3.1** for the projective case: the agreement locus of two regular
functions is closed.

Agreement of `g₁/h₁` and `g₂/h₂` is the vanishing of `g₁h₂ − g₂h₁`, and that is
homogeneous of degree `n₁ + n₂` precisely because each pair has matched degrees.
Without that the difference is not homogeneous, so it does not cut out a Zariski
closed set and the argument collapses. -/
theorem isClosed_eqLocusProjVia (hι : Continuous ι) {f f' : A → k}
    (hf : IsRegularProjVia ι f) (hf' : IsRegularProjVia ι f') :
    IsClosed {P : A | f P = f' P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro P hP
  obtain ⟨U, hU, hPU, n₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := hf P
  obtain ⟨V, hV, hPV, n₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := hf' P
  have hhom : IsHomogeneousSet ({g₁ * h₂ - g₂ * h₁} : Set (MvPolynomial σ k)) := by
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨n₁ + n₂, (hg₁.mul hh₂).sub (by simpa [Nat.add_comm] using hg₂.mul hh₁)⟩
  refine ⟨(U ∩ V) ∩ (ι ⁻¹' (projZeroSet {g₁ * h₂ - g₂ * h₁})ᶜ), ?_, ?_, ?_⟩
  · rintro Q ⟨⟨hQU, hQV⟩, hQz⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, mem_projZeroSet_iff] at hQz
    intro hQeq
    refine hQz fun p hp => ?_
    rw [Set.mem_singleton_iff] at hp
    subst hp
    show eval _ _ = 0
    rw [Set.mem_ofPred_eq, he₁ Q hQU, he₂ Q hQV,
      div_eq_div_iff (hne₁ Q hQU) (hne₂ Q hQV)] at hQeq
    simp only [map_sub, map_mul]
    rw [hQeq, sub_self]
  · exact (hU.inter hV).inter
      (((isClosed_projZeroSet_of_isHomogeneousSet hhom).isOpen_compl).preimage hι)
  · refine ⟨⟨hPU, hPV⟩, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, mem_projZeroSet_iff, not_forall]
    refine ⟨g₁ * h₂ - g₂ * h₁, rfl, ?_⟩
    show ¬ (eval _ _ = 0)
    simp only [map_sub, map_mul, sub_eq_zero]
    intro hcon
    exact hP (by
      rw [Set.mem_ofPred_eq, he₁ P hPU, he₂ P hPV,
        div_eq_div_iff (hne₁ P hPU) (hne₂ P hPV), hcon])

/-- Lemma 3.1's content for a subset of projective space. -/
theorem isClosed_eqLocusProj {Y : Set (ProjectiveSpace k σ)} {f f' : Y → k}
    (hf : IsRegularProj f) (hf' : IsRegularProj f') :
    IsClosed {P : Y | f P = f' P} :=
  isClosed_eqLocusProjVia continuous_subtype_val hf hf'

end Hartshorne
