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

## Regularity relative to a map

The definition is stated for a space `A` equipped with a map `ι : A → 𝔸ⁿ`
rather than for a subset of `𝔸ⁿ`. Hartshorne only ever needs the subtype
inclusion, but the `Variety` structure needs regularity on an *open subset of a
subset*, where the map to affine space is a composite of two coercions.
Parametrising by `ι` avoids transporting along `↥U ≃ ↥(val '' U)` by hand at
every such step.

`IsRegular` is the special case `ι = Subtype.val`, which is Hartshorne's
definition verbatim.

## On Lemma 3.1

Hartshorne states it as "a regular function is continuous, when `k` is
identified with `𝔸¹`". His proof shows each fibre is closed, then invokes "a
closed set of `𝔸¹` is a finite set of points". Only the first step and its
consequence are formalized here; see the roadmap article for why the second is
deferred.

## Main definitions

* `Hartshorne.IsRegularVia`, `Hartshorne.IsRegular`

## Main results

* `Hartshorne.isClosed_eqLocusVia` : the agreement locus of two regular
  functions is closed. This is Lemma 3.1's content.
* `Hartshorne.eq_of_eqOn_isOpen` : Remark 3.1.1, the identity principle.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- `f` is *regular at* `P`, relative to a map `ι` to affine space, when near
`P` it is a quotient of polynomials in the coordinates of `ι`, with the
denominator nowhere zero. -/
def IsRegularAtVia {A : Type*} [TopologicalSpace A] (ι : A → (σ → k))
    (f : A → k) (P : A) : Prop :=
  ∃ U : Set A, IsOpen U ∧ P ∈ U ∧ ∃ g h : MvPolynomial σ k,
    (∀ x ∈ U, eval (ι x) h ≠ 0) ∧ ∀ x ∈ U, f x = eval (ι x) g / eval (ι x) h

/-- `f` is *regular* relative to `ι` when it is regular at every point. -/
def IsRegularVia {A : Type*} [TopologicalSpace A] (ι : A → (σ → k))
    (f : A → k) : Prop :=
  ∀ P, IsRegularAtVia ι f P

/-- Hartshorne's regularity at a point, for a subset of affine space. -/
def IsRegularAt {Y : Set (σ → k)} (f : Y → k) (P : Y) : Prop :=
  IsRegularAtVia (Subtype.val) f P

/-- Hartshorne's regularity, for a subset of affine space. -/
def IsRegular {Y : Set (σ → k)} (f : Y → k) : Prop :=
  IsRegularVia (Subtype.val) f

/-- **Lemma 3.1**, in the form its proof establishes: the locus where two
regular functions agree is closed.

Locally `f = g₁/h₁` and `f' = g₂/h₂` with both denominators nonvanishing, so
agreement is the vanishing of `g₁h₂ - g₂h₁`, a closed condition pulled back
along `ι`. Closedness is local, so that suffices. -/
theorem isClosed_eqLocusVia {A : Type*} [TopologicalSpace A] {ι : A → (σ → k)}
    (hι : Continuous ι) {f f' : A → k}
    (hf : IsRegularVia ι f) (hf' : IsRegularVia ι f') :
    IsClosed {P : A | f P = f' P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro P hP
  obtain ⟨U, hU, hPU, g₁, h₁, hh₁, he₁⟩ := hf P
  obtain ⟨V, hV, hPV, g₂, h₂, hh₂, he₂⟩ := hf' P
  refine ⟨(U ∩ V) ∩ (ι ⁻¹' (zeroSet {g₁ * h₂ - g₂ * h₁})ᶜ), ?_, ?_, ?_⟩
  · rintro Q ⟨⟨hQU, hQV⟩, hQz⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, mem_zeroSet_iff] at hQz
    intro hQeq
    refine hQz fun p hp => ?_
    rw [Set.mem_singleton_iff] at hp
    subst hp
    rw [Set.mem_ofPred_eq, he₁ Q hQU, he₂ Q hQV,
      div_eq_div_iff (hh₁ Q hQU) (hh₂ Q hQV)] at hQeq
    simp only [map_sub, map_mul]
    rw [hQeq, sub_self]
  · exact (hU.inter hV).inter (((isClosed_zeroSet _).isOpen_compl).preimage hι)
  · refine ⟨⟨hPU, hPV⟩, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, mem_zeroSet_iff, not_forall]
    refine ⟨g₁ * h₂ - g₂ * h₁, rfl, ?_⟩
    simp only [map_sub, map_mul, sub_eq_zero]
    intro hcon
    exact hP (by
      rw [Set.mem_ofPred_eq, he₁ P hPU, he₂ P hPV,
        div_eq_div_iff (hh₁ P hPU) (hh₂ P hPV), hcon])

/-- Lemma 3.1's content for a subset of affine space. -/
theorem isClosed_eqLocus {Y : Set (σ → k)} {f f' : Y → k}
    (hf : IsRegular f) (hf' : IsRegular f') :
    IsClosed {P : Y | f P = f' P} :=
  isClosed_eqLocusVia continuous_subtype_val hf hf'

/-- **Remark 3.1.1**, the identity principle: two regular functions on an
irreducible space agreeing on a nonempty open set agree everywhere.

This is what makes `𝒪(Y) → 𝒪_P → K(Y)` injective, so that all three rings can
be treated as subrings of the function field. Every later argument in §3 that
manipulates germs as if they were functions rests on it. -/
theorem eq_of_eqOn_isOpen {A : Type*} [TopologicalSpace A]
    (hA : IsPreirreducible (Set.univ : Set A)) {ι : A → (σ → k)} (hι : Continuous ι)
    {f f' : A → k} (hf : IsRegularVia ι f) (hf' : IsRegularVia ι f')
    {U : Set A} (hU : IsOpen U) (hne : U.Nonempty) (heq : Set.EqOn f f' U) :
    f = f' := by
  have hclosed := isClosed_eqLocusVia hι hf hf'
  have hdense : Dense U := by
    rw [dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    intro x _
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨z, -, hz⟩ := hA o U ho hU ⟨x, Set.mem_univ x, hxo⟩
      (hne.mono fun _ h => ⟨Set.mem_univ _, h⟩)
    exact ⟨z, hz.1, hz.2⟩
  have hsub : closure U ⊆ {Q : A | f Q = f' Q} := by
    rw [← hclosed.closure_eq]
    exact closure_mono fun x hx => heq hx
  funext P
  exact hsub (hdense P)

end Hartshorne
