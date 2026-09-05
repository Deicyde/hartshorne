/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.MorphismToAffine
import Hartshorne.Projective.IrreducibleSpace
import Hartshorne.Projective.Dehomogenize

/-!
# Proposition 3.3: the standard charts are isomorphisms of varieties

Hartshorne, *Algebraic Geometry*, I.3, Proposition 3.3 (p. 18).

The homeomorphism `φᵢ : Uᵢ → 𝔸ⁿ` of Proposition 2.2 is an isomorphism of
varieties. Only the regular functions remain to be checked, and the two
directions are checked by different means.

Forward is [Lemma 3.6](../morphisms/morphism-to-affine-criterion.md): the
coordinates of `φᵢ` are `x_j/x_i`, ratios of homogeneous polynomials of degree
one whose denominator is nowhere zero on `Uᵢ` by the definition of the chart.
That the lemma is stated for an arbitrary source is what makes it apply here.

Backward is not covered by that lemma, whose target must be affine. It is
checked directly, and this is where `dehomogenize` earns its keep: a regular
function on an open subset of `Uᵢ` is locally `g/h` with `g` and `h` homogeneous
of the same degree, and pulling back along `β` turns that into
`α(g)/α(h)`, a ratio of polynomials in the affine coordinates. Two facts make
that work — the ratio of two homogeneous polynomials of equal degree is
insensitive to the choice of representative, and `β(y)` may be represented by
the vector with `1` in slot `i`.

## Main definitions

* `Hartshorne.chartVariety`, `Hartshorne.chartTarget`
* `Hartshorne.chartHom`, `Hartshorne.chartInvHom`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable (k : Type*) [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ] [DecidableEq σ]
  [Nonempty σ] (i : σ)

/-- The standard chart is a quasi-projective variety: an open subset of `ℙⁿ`,
which is itself a projective variety. -/
theorem isQuasiProjVariety_standardChart :
    IsQuasiProjVariety (standardChart i : Set (ProjectiveSpace k σ)) :=
  ⟨⟨chartInv i 0, chartInv_mem_standardChart i 0⟩, Set.univ, standardChart i,
    isProjVariety_univ, isOpen_standardChart i, (Set.univ_inter _).symm⟩

omit [DecidableEq σ] [Nonempty σ] in
/-- The chart's affine space is a quasi-affine variety. -/
theorem isQuasiAffineVariety_univ_chart :
    IsQuasiAffineVariety (Set.univ : Set ({j : σ // j ≠ i} → k)) :=
  ⟨Set.univ_nonempty, Set.univ, Set.univ, ⟨isIrreducible_univ, isClosed_univ⟩,
    isOpen_univ, (Set.univ_inter _).symm⟩

/-- `Uᵢ`, as a variety. -/
noncomputable abbrev chartVariety : Variety k :=
  Variety.ofQuasiProjective (isQuasiProjVariety_standardChart k i)

/-- The chart's affine space, as a variety. -/
noncomputable abbrev chartTarget : Variety k :=
  Variety.ofQuasiAffine (isQuasiAffineVariety_univ_chart k i)

/-- `φᵢ`, on the underlying carriers. -/
noncomputable def chartFun (P : (chartVariety k i).carrier) :
    (Set.univ : Set ({j : σ // j ≠ i} → k)) :=
  ⟨chartMap i P.1, Set.mem_univ _⟩

/-- The coordinates of `φᵢ` are regular: `x_j/x_i` is a ratio of homogeneous
polynomials of degree one, and the denominator is nowhere zero on `Uᵢ`. -/
theorem isGlobalRegular_chartCoord (j : {j : σ // j ≠ i}) :
    (chartVariety k i).IsGlobalRegular fun P => (chartFun k i P : {j : σ // j ≠ i} → k) j := by
  intro z
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, X j.1, X i,
    isHomogeneous_X _ _, isHomogeneous_X _ _, fun x _ => ?_, fun x _ => ?_⟩
  · simpa using rep_ne_zero_of_mem_standardChart x.1.2
  · simp [chartFun, chartMap]

theorem continuous_chartFun : Continuous (chartFun k i) :=
  (Variety.continuous_of_coords_regular _ (isGlobalRegular_chartCoord k i)).subtype_mk _

/-- **`φᵢ` is a morphism of varieties**, by Lemma 3.6. -/
noncomputable def chartHom : VarietyHom (chartVariety k i) (chartTarget k i) :=
  ⟨chartFun k i, continuous_chartFun k i,
    fun V _f hf => regular_comp_of_coords_regular (chartFun k i) (continuous_chartFun k i)
      (isGlobalRegular_chartCoord k i) V hf⟩

/-- `β`, on the underlying carriers. -/
noncomputable def chartInvFun (y : (chartTarget k i).carrier) : (chartVariety k i).carrier :=
  ⟨chartInv i y.1, chartInv_mem_standardChart i y.1⟩

theorem continuous_chartInvFun : Continuous (chartInvFun k i) :=
  ((continuous_chartInv i).comp continuous_subtype_val).subtype_mk _

omit [IsAlgClosed k] [Finite σ] [Nonempty σ] in
/-- The ratio of two homogeneous polynomials of equal degree, evaluated at a
representative of `β(y)`, is the ratio of their dehomogenisations at `y`.

Two facts combine here: the ratio does not see the choice of representative,
and `β(y)` is represented by the vector with `1` in slot `i`, which is exactly
what dehomogenising computes with. -/
theorem eval_rep_chartInv_div {n : ℕ} {g h : MvPolynomial σ k} (hg : g.IsHomogeneous n)
    (hh : h.IsHomogeneous n) (y : {j : σ // j ≠ i} → k) :
    eval (chartInv i y).rep g / eval (chartInv i y).rep h
      = eval y (dehomogenize i g) / eval y (dehomogenize i h) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k (chartInvVec i y)
    (chartInvVec_ne_zero i y)
  have hr : eval (chartInv i y).rep g / eval (chartInv i y).rep h
      = eval (chartInvVec i y) g / eval (chartInvVec i y) h := by
    rw [chartInv, ← ha]
    exact ratio_eq_of_smul hg hh (Units.ne_zero a) (chartInvVec i y)
  rw [hr, eval_dehomogenize, eval_dehomogenize]

omit [IsAlgClosed k] [Finite σ] [Nonempty σ] in
/-- A denominator that does not vanish at `β(y)` dehomogenises to one that does
not vanish at `y`. -/
theorem eval_dehomogenize_ne_zero {n : ℕ} {h : MvPolynomial σ k} (hh : h.IsHomogeneous n)
    (y : {j : σ // j ≠ i} → k) (hz : eval (chartInv i y).rep h ≠ 0) :
    eval y (dehomogenize i h) ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k (chartInvVec i y)
    (chartInvVec_ne_zero i y)
  have hzz : eval ((a : k) • chartInvVec i y) h ≠ 0 := by
    rw [chartInv, ← ha] at hz
    exact hz
  rw [hh.eval_smul] at hzz
  rw [eval_dehomogenize]
  exact fun hzero => hzz (by rw [hzero, mul_zero])

/-- **`β` is a morphism of varieties.**

Lemma 3.6 does not apply, since the target is projective, so the pullback of a
regular function is checked directly: locally it is `g/h` with `g` and `h`
homogeneous of the same degree, and dehomogenising turns that into a ratio of
polynomials in the affine coordinates. -/
noncomputable def chartInvHom : VarietyHom (chartTarget k i) (chartVariety k i) where
  toFun := chartInvFun k i
  continuous_toFun := continuous_chartInvFun k i
  regular_comp V f hf := by
    intro Q
    obtain ⟨W, hW, hQW, n, g, h, hg, hh, hne, he⟩ :=
      (mem_projRegularSubalgebra.1 hf) ⟨chartInvFun k i Q.1, Q.2⟩
    have hcont : Continuous fun x : (Opens.comap ⟨chartInvFun k i,
        continuous_chartInvFun k i⟩ V) => (⟨chartInvFun k i x.1, x.2⟩ : V) :=
      ((continuous_chartInvFun k i).comp continuous_subtype_val).subtype_mk _
    refine ⟨(fun x : (Opens.comap ⟨chartInvFun k i, continuous_chartInvFun k i⟩ V) =>
        (⟨chartInvFun k i x.1, x.2⟩ : V)) ⁻¹' W, hW.preimage hcont, hQW,
      dehomogenize i g, dehomogenize i h, fun x hx => ?_, fun x hx => ?_⟩
    · exact eval_dehomogenize_ne_zero k i hh x.1.1
        (hne ⟨chartInvFun k i x.1, x.2⟩ hx)
    · exact (he ⟨chartInvFun k i x.1, x.2⟩ hx).trans
        (eval_rep_chartInv_div k i hg hh x.1.1)

theorem chartHom_comp_chartInvHom :
    (chartHom k i).comp (chartInvHom k i) = VarietyHom.id (chartTarget k i) :=
  VarietyHom.ext (funext fun y => Subtype.ext (chartMap_chartInv i y.1))

theorem chartInvHom_comp_chartHom :
    (chartInvHom k i).comp (chartHom k i) = VarietyHom.id (chartVariety k i) :=
  VarietyHom.ext (funext fun P => Subtype.ext (chartInv_chartMap P.2))

/-- **Proposition 3.3**: the standard chart `φᵢ : Uᵢ → 𝔸ⁿ` is an isomorphism of
varieties, not merely a homeomorphism.

The distinction is not idle. Exercise 3.2 exhibits bijective bicontinuous
morphisms that are not isomorphisms, so a homeomorphism carries no information
about regular functions on its own; what makes this one an isomorphism is that
both directions pull regular functions back to regular functions. -/
theorem isIso_chartHom : (chartHom k i).IsIso :=
  ⟨chartInvHom k i, chartInvHom_comp_chartHom k i, chartHom_comp_chartInvHom k i⟩

end Hartshorne
