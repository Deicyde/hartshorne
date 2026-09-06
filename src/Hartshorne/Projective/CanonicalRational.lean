/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyFunctionFieldStructure
import Hartshorne.Morphism.ProjVariety
import Hartshorne.Projective.CoordAwayChart

/-!
# A ratio of homogeneous forms is a rational function

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(a) and (c).

For `g`, `h` homogeneous of the same degree with `h` not vanishing identically
on `Y`, the assignment `P ↦ g(P)/h(P)` is a rational function on `Y`. This is
the chart-free half of the identification `S(Y)_((0)) ≅ K(Y)`.

The chart-based construction of that identification is enough for Theorem
3.4(b) and (c), which work one chart at a time. It is *not* enough for 3.4(a),
which needs a single element of `S(Y)_((0))` satisfying a condition on every
chart at once: the per-chart identifications are different terms, and nothing
says they agree. Built this way there is only one map and the question does not
arise.

Everything here is a pointwise check. The ratio is well defined on projective
space because the degrees agree, so rescaling a representative cancels; it is
regular because being locally such a ratio is the definition of regular on a
projective variety, and here it is such a ratio globally.

## Main definitions

* `Hartshorne.projRatOfFraction`

## Main results

* `Hartshorne.isOpen_projNonvanishing`
* `Hartshorne.projRatOfFraction_rel`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (ProjectiveSpace k σ)}

/-- The locus where a homogeneous polynomial does not vanish is open: its
complement is the zero set of a homogeneous singleton. -/
theorem isOpen_projNonvanishing {n : ℕ} {h : MvPolynomial σ k} (hh : h.IsHomogeneous n) :
    IsOpen {P : ProjectiveSpace k σ | eval P.rep h ≠ 0} := by
  rw [isOpen_iff_isProjAlgebraicSet_compl]
  refine ⟨{h}, fun f hf => ⟨n, hf ▸ hh⟩, ?_⟩
  ext P
  simp [projZeroSet, HomogeneousVanish]

/-- **A ratio of homogeneous forms of equal degree, as a rational function.**

The domain is where the denominator does not vanish, which is open and, by
hypothesis, nonempty; regularity holds on the whole domain at once, with the
given `g` and `h` as the local data. -/
noncomputable def projRatOfFraction (hY : IsQuasiProjVariety Y) {n : ℕ}
    {g h : MvPolynomial σ k} (hg : g.IsHomogeneous n) (hh : h.IsHomogeneous n)
    (hne : ∃ P ∈ Y, eval P.rep h ≠ 0) :
    Variety.RationalRep (Variety.ofQuasiProjective hY) where
  U := ⟨{P : Y | eval P.1.rep h ≠ 0},
    (isOpen_projNonvanishing hh).preimage continuous_subtype_val⟩
  nonempty_U := by
    obtain ⟨P, hPY, hP⟩ := hne
    exact ⟨⟨P, hPY⟩, hP⟩
  toFun := fun x => eval x.1.1.rep g / eval x.1.1.rep h
  regular := fun _ =>
    ⟨Set.univ, isOpen_univ, trivial, n, g, h, hg, hh, fun x _ => x.2, fun _ _ => rfl⟩

@[simp]
theorem projRatOfFraction_toFun (hY : IsQuasiProjVariety Y) {n : ℕ}
    {g h : MvPolynomial σ k} (hg : g.IsHomogeneous n) (hh : h.IsHomogeneous n)
    (hne : ∃ P ∈ Y, eval P.rep h ≠ 0)
    (x : (projRatOfFraction hY hg hh hne).U) :
    (projRatOfFraction hY hg hh hne).toFun x
      = eval x.1.1.rep g / eval x.1.1.rep h :=
  rfl

/-- **Cross-multiplied ratios define the same rational function.**

The hypothesis is an equation in `S(Y)`, which is what the localisation
produces; it is turned into a pointwise statement by the fact that an element of
`J(Y)` vanishes on `Y`, and then the two ratios agree wherever both are
defined. -/
theorem projRatOfFraction_rel (hY : IsQuasiProjVariety Y) {n m : ℕ}
    {g h g' h' : MvPolynomial σ k} (hg : g.IsHomogeneous n) (hh : h.IsHomogeneous n)
    (hg' : g'.IsHomogeneous m) (hh' : h'.IsHomogeneous m)
    (hne : ∃ P ∈ Y, eval P.rep h ≠ 0) (hne' : ∃ P ∈ Y, eval P.rep h' ≠ 0)
    (heq : (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (g * h'))
      = Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (g' * h)) :
    (projRatOfFraction hY hg hh hne).Rel (projRatOfFraction hY hg' hh' hne') := by
  intro x hx hx'
  have hmem : g * h' - g' * h ∈ homogeneousVanishingIdeal Y := Ideal.Quotient.eq.1 heq
  have hvan : eval x.1.rep (g * h' - g' * h) = 0 :=
    homogeneousVanish_of_mem_homogeneousVanishingIdeal hmem x.2
  rw [map_sub, sub_eq_zero, map_mul, map_mul] at hvan
  show eval x.1.rep g / eval x.1.rep h = eval x.1.rep g' / eval x.1.rep h'
  rw [div_eq_div_iff hx hx']
  exact hvan

end Hartshorne
