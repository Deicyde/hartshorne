/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.MorphismToAffine
import Hartshorne.Projective.IrreducibleSpace
import Hartshorne.Projective.Dehomogenize
import Hartshorne.Projective.AffineCover

/-!
# The standard charts are isomorphisms of varieties

Hartshorne, *Algebraic Geometry*, I.3, Proposition 3.3 (p. 18).

Proposition 2.2 gives a homeomorphism `φᵢ : Uᵢ → 𝔸ⁿ`; Proposition 3.3 upgrades
it to an isomorphism of varieties. Exercise 3.2 shows the upgrade has content:
there are bijective bicontinuous morphisms that are not isomorphisms, so a
homeomorphism says nothing about regular functions by itself.

Both directions are proved for a quasi-projective `Y` and its piece
`Yᵢ = Y ∩ Uᵢ`, not only for `Uᵢ` itself. Hartshorne states 3.3 for the chart and
then uses it on `Yᵢ` without comment, which is legitimate but is not the same
statement, and Theorem 3.4 needs the version with `Y` in it. Taking `Y = ℙⁿ`
recovers the stated proposition.

`φᵢ` is a morphism by Lemma 3.6: its coordinates `x_j/x_i` are ratios of
homogeneous polynomials of degree one whose denominator is nowhere zero on the
chart. `β` is not covered by Lemma 3.6, since its target is projective, and is
checked directly: a regular function is locally `g/h` with `g`, `h` homogeneous
of equal degree, and dehomogenising turns that ratio into a ratio of polynomials
in the affine coordinates. What makes the two facts about `β` work is that `β(y)`
is represented by the vector with `1` in slot `i`, which is what dehomogenising
computes with, together with the fact that a ratio of equal-degree homogeneous
polynomials does not see the choice of representative.

## Main definitions

* `Hartshorne.chartVariety`, `Hartshorne.chartTarget`
* `Hartshorne.chartHom`, `Hartshorne.chartInvHom`

## Main results

* `Hartshorne.isIso_chartHom`
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

variable {Y : Set (ProjectiveSpace k σ)} (hY : IsQuasiProjVariety Y)
  (hne : (Y ∩ standardChart i).Nonempty)

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
include hY hne in
/-- `Yᵢ = Y ∩ Uᵢ` is again quasi-projective: cutting a quasi-projective set by an
open set only shrinks the open half of its presentation. -/
theorem isQuasiProjVariety_inter_standardChart :
    IsQuasiProjVariety (Y ∩ standardChart i) := by
  obtain ⟨-, V, U, hV, hU, rfl⟩ := hY
  exact ⟨hne, V, U ∩ standardChart i, hV, hU.inter (isOpen_standardChart i),
    Set.inter_assoc _ _ _⟩

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
/-- `Yᵢ` is open in `Y`, being cut out by an open set of projective space. This
is what makes `Y ∩ Uᵢ` an open subvariety rather than merely a subvariety. -/
theorem isOpen_inter_standardChart_in :
    IsOpen {y : Y | y.1 ∈ Y ∩ standardChart i} := by
  have hset : {y : Y | y.1 ∈ Y ∩ standardChart i}
      = Subtype.val ⁻¹' (standardChart i : Set (ProjectiveSpace k σ)) := by
    ext y
    exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
  rw [hset]
  exact (isOpen_standardChart i).preimage continuous_subtype_val

/-- `Yᵢ`, as a variety. -/
noncomputable abbrev chartVariety : Variety k :=
  Variety.ofQuasiProjective (isQuasiProjVariety_inter_standardChart k i hY hne)

/-- `φᵢ(Yᵢ)`, as a variety. It is affine when `Y` is projective (Corollary 2.3);
in general it is quasi-affine, which is all that is used here. -/
noncomputable abbrev chartTarget : Variety k :=
  Variety.ofQuasiAffine (isQuasiAffineVariety_chartMap_image i hY hne)

/-- `φᵢ`, on the underlying carriers. -/
noncomputable def chartFun (P : (chartVariety k i hY hne).carrier) :
    (chartTarget k i hY hne).carrier :=
  ⟨chartMap i P.1, P.1, P.2, rfl⟩

/-- The coordinates of `φᵢ` are regular: `x_j/x_i` is a ratio of homogeneous
polynomials of degree one, and the denominator is nowhere zero on `Uᵢ`. -/
theorem isGlobalRegular_chartCoord (j : {j : σ // j ≠ i}) :
    (chartVariety k i hY hne).IsGlobalRegular
      fun P => (chartFun k i hY hne P).1 j := by
  intro z
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, X j.1, X i,
    isHomogeneous_X _ _, isHomogeneous_X _ _, fun x _ => ?_, fun x _ => ?_⟩
  · simpa using rep_ne_zero_of_mem_standardChart x.1.2.2
  · simp [chartFun, chartMap]

theorem continuous_chartFun : Continuous (chartFun k i hY hne) :=
  (Variety.continuous_of_coords_regular _ (isGlobalRegular_chartCoord k i hY hne)).subtype_mk _

/-- **`φᵢ` is a morphism of varieties**, by Lemma 3.6. -/
noncomputable def chartHom : VarietyHom (chartVariety k i hY hne) (chartTarget k i hY hne) :=
  ⟨chartFun k i hY hne, continuous_chartFun k i hY hne,
    fun V _f hf => regular_comp_of_coords_regular (chartFun k i hY hne)
      (continuous_chartFun k i hY hne) (isGlobalRegular_chartCoord k i hY hne) V hf⟩

/-- `β`, on the underlying carriers. Its image lands back in `Yᵢ` because a point
of `φᵢ(Yᵢ)` is `φᵢ` of a point of `Yᵢ`, and `β` undoes `φᵢ` there. -/
noncomputable def chartInvFun (y : (chartTarget k i hY hne).carrier) :
    (chartVariety k i hY hne).carrier :=
  ⟨chartInv i y.1, by
    obtain ⟨P, hP, hPy⟩ := y.2
    rw [← hPy, chartInv_chartMap hP.2]
    exact hP⟩

theorem continuous_chartInvFun : Continuous (chartInvFun k i hY hne) :=
  ((continuous_chartInv i).comp continuous_subtype_val).subtype_mk _

/-- **`β` is a morphism of varieties.**

Lemma 3.6 does not apply, since the target is projective, so the pullback of a
regular function is checked directly: locally it is `g/h` with `g` and `h`
homogeneous of the same degree, and dehomogenising turns that into a ratio of
polynomials in the affine coordinates. -/
noncomputable def chartInvHom : VarietyHom (chartTarget k i hY hne) (chartVariety k i hY hne) where
  toFun := chartInvFun k i hY hne
  continuous_toFun := continuous_chartInvFun k i hY hne
  regular_comp V f hf := by
    intro Q
    obtain ⟨W, hW, hQW, n, g, h, hg, hh, hne', he⟩ :=
      (mem_projRegularSubalgebra.1 hf) ⟨chartInvFun k i hY hne Q.1, Q.2⟩
    have hcont : Continuous fun x : (Opens.comap ⟨chartInvFun k i hY hne,
        continuous_chartInvFun k i hY hne⟩ V) => (⟨chartInvFun k i hY hne x.1, x.2⟩ : V) :=
      ((continuous_chartInvFun k i hY hne).comp continuous_subtype_val).subtype_mk _
    refine ⟨(fun x : (Opens.comap ⟨chartInvFun k i hY hne,
          continuous_chartInvFun k i hY hne⟩ V) =>
        (⟨chartInvFun k i hY hne x.1, x.2⟩ : V)) ⁻¹' W, hW.preimage hcont, hQW,
      dehomogenize i g, dehomogenize i h, fun x hx => ?_, fun x hx => ?_⟩
    · exact eval_dehomogenize_ne_zero k i hh x.1.1
        (hne' ⟨chartInvFun k i hY hne x.1, x.2⟩ hx)
    · exact (he ⟨chartInvFun k i hY hne x.1, x.2⟩ hx).trans
        (eval_rep_chartInv_div k i hg hh x.1.1)

theorem chartHom_comp_chartInvHom :
    (chartHom k i hY hne).comp (chartInvHom k i hY hne)
      = VarietyHom.id (chartTarget k i hY hne) :=
  VarietyHom.ext (funext fun y => Subtype.ext (chartMap_chartInv i y.1))

theorem chartInvHom_comp_chartHom :
    (chartInvHom k i hY hne).comp (chartHom k i hY hne)
      = VarietyHom.id (chartVariety k i hY hne) :=
  VarietyHom.ext (funext fun P => Subtype.ext (chartInv_chartMap P.2.2))

/-- **Proposition 3.3**: `φᵢ : Yᵢ → φᵢ(Yᵢ)` is an isomorphism of varieties, not
merely a homeomorphism. Hartshorne states this for `Y = ℙⁿ`, where it reads
`Uᵢ ≅ 𝔸ⁿ`.

The distinction is not idle. Exercise 3.2 exhibits bijective bicontinuous
morphisms that are not isomorphisms, so a homeomorphism carries no information
about regular functions on its own; what makes this one an isomorphism is that
both directions pull regular functions back to regular functions. -/
theorem isIso_chartHom : (chartHom k i hY hne).IsIso :=
  ⟨chartInvHom k i hY hne, chartInvHom_comp_chartHom k i hY hne,
    chartHom_comp_chartInvHom k i hY hne⟩

end Hartshorne
