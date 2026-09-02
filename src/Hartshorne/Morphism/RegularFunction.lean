/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Variety

/-!
# Regular functions on a quasi-affine variety

Hartshorne, *Algebraic Geometry*, I.3, the definition on p. 15 with Lemma 3.1
and Remark 3.1.1.

A function is *regular at* a point when it agrees with a quotient of
polynomials on some neighbourhood, with the denominator nowhere zero there. The
representing pair may vary from point to point: a regular function need not be a
single global quotient, and Hartshorne's later examples turn on exactly that.

## On Lemma 3.1

Hartshorne states it as "a regular function is continuous, when `k` is
identified with `𝔸¹`". His proof establishes that each fibre `f⁻¹(a)` is closed
and then invokes "a closed set of `𝔸¹` is a finite set of points" to conclude
continuity.

What is proved here is the first half, `isClosed_fiber`, and the consequence
that matters, `eq_of_eqOn_isOpen`. Deducing genuine `Continuous` would also need
that closed subsets of `𝔸¹` are finite, which requires putting a topology on
`k` and identifying it with the one on `Unit → k`. Nothing in §3 uses
continuity as such — every later appeal is to the identity principle — so that
step is deferred rather than done for its own sake.

## Main definitions

* `Hartshorne.IsRegularAt`, `Hartshorne.IsRegular`

## Main results

* `Hartshorne.isClosed_eqLocus` : the agreement locus of two regular functions
  is closed. This is Lemma 3.1's content.
* `Hartshorne.eq_of_eqOn_isOpen` : Remark 3.1.1, the identity principle.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- `f` is *regular at* `P` when it is a quotient of polynomials near `P`, with
the denominator nowhere zero on that neighbourhood. -/
def IsRegularAt {Y : Set (σ → k)} (f : Y → k) (P : Y) : Prop :=
  ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧ ∃ g h : MvPolynomial σ k,
    (∀ x ∈ U, eval (x : σ → k) h ≠ 0) ∧
      ∀ x ∈ U, f x = eval (x : σ → k) g / eval (x : σ → k) h

/-- `f` is *regular* when it is regular at every point. -/
def IsRegular {Y : Set (σ → k)} (f : Y → k) : Prop :=
  ∀ P, IsRegularAt f P

/-- **Lemma 3.1**, in the form its proof establishes: the locus where two
regular functions agree is closed.

Locally `f = g₁/h₁` and `f' = g₂/h₂` with both denominators nonvanishing, so
agreement is the vanishing of `g₁h₂ - g₂h₁`, a closed condition. Closedness is
local, so that suffices. -/
theorem isClosed_eqLocus {Y : Set (σ → k)} {f f' : Y → k}
    (hf : IsRegular f) (hf' : IsRegular f') :
    IsClosed {P : Y | f P = f' P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro P hP
  obtain ⟨U, hU, hPU, g₁, h₁, hh₁, he₁⟩ := hf P
  obtain ⟨V, hV, hPV, g₂, h₂, hh₂, he₂⟩ := hf' P
  -- On `U ∩ V` the two functions agree exactly when `g₁h₂ - g₂h₁` vanishes.
  refine ⟨(U ∩ V) ∩ (Subtype.val ⁻¹' (zeroSet {g₁ * h₂ - g₂ * h₁})ᶜ), ?_, ?_, ?_⟩
  · rintro Q ⟨⟨hQU, hQV⟩, hQz⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, mem_zeroSet_iff] at hQz
    intro hQeq
    refine hQz fun p hp => ?_
    rw [Set.mem_singleton_iff] at hp
    subst hp
    have h1 := he₁ Q hQU
    have h2 := he₂ Q hQV
    have hne1 := hh₁ Q hQU
    have hne2 := hh₂ Q hQV
    rw [Set.mem_ofPred_eq, h1, h2, div_eq_div_iff hne1 hne2] at hQeq
    simp only [map_sub, map_mul]
    rw [hQeq, sub_self]
  · exact ((hU.inter hV).inter
      (((isClosed_zeroSet _).isOpen_compl).preimage continuous_subtype_val))
  · refine ⟨⟨hPU, hPV⟩, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, mem_zeroSet_iff, not_forall]
    refine ⟨g₁ * h₂ - g₂ * h₁, rfl, ?_⟩
    have h1 := he₁ P hPU
    have h2 := he₂ P hPV
    have hne1 := hh₁ P hPU
    have hne2 := hh₂ P hPV
    simp only [map_sub, map_mul, sub_eq_zero]
    intro hcon
    exact hP (by rw [Set.mem_ofPred_eq, h1, h2, div_eq_div_iff hne1 hne2, hcon])

/-- **Remark 3.1.1**, the identity principle: two regular functions on an
irreducible space agreeing on a nonempty open set agree everywhere.

This is what makes `𝒪(Y) → 𝒪_P → K(Y)` injective, so that all three rings can
be treated as subrings of the function field. Every later argument in §3 that
manipulates germs as if they were functions rests on it. -/
theorem eq_of_eqOn_isOpen {Y : Set (σ → k)} (hY : IsPreirreducible (Set.univ : Set Y))
    {f f' : Y → k} (hf : IsRegular f) (hf' : IsRegular f')
    {U : Set Y} (hU : IsOpen U) (hne : U.Nonempty) (heq : Set.EqOn f f' U) :
    f = f' := by
  have hclosed := isClosed_eqLocus hf hf'
  have hdense : Dense U := by
    rw [dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    intro x _
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨z, -, hz⟩ := hY o U ho hU ⟨x, Set.mem_univ x, hxo⟩
      (hne.mono fun _ h => ⟨Set.mem_univ _, h⟩)
    exact ⟨z, hz.1, hz.2⟩
  have hsub : closure U ⊆ {Q : Y | f Q = f' Q} := by
    rw [← hclosed.closure_eq]
    exact closure_mono fun x hx => heq hx
  funext P
  exact hsub (hdense P)

end Hartshorne
