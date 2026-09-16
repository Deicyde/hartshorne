/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.Minors
import Hartshorne.Morphism.VarietyRational
import Hartshorne.Morphism.Hom
import Hartshorne.Morphism.ProjVariety

/-!
# Two morphisms agreeing on an open set are equal

Hartshorne, *Algebraic Geometry*, I.4, Lemma 4.1 (p. 24).

If `φ, ψ : X → Y` are morphisms of varieties agreeing on a nonempty open subset
of `X`, they are equal.

This is the rigidity that makes rational maps well behaved, and it is the
algebraic stand-in for Hausdorff separation: the Zariski topology is not
Hausdorff, and the statement is really that the diagonal of `Y × Y` is closed.

## The route taken

Hartshorne reduces to `Y = ℙⁿ`, gives `ℙⁿ × ℙⁿ` its Segre structure, notes that
the diagonal is cut out by the minors `xᵢyⱼ = xⱼyᵢ`, and concludes from
`(φ × ψ)(U) ⊆ Δ` with `U` dense.

The proof here uses the same equations without building the product. The
agreement locus is closed because it is closed on each member of the open cover
`W_{ij} = φ⁻¹(Uᵢ) ∩ ψ⁻¹(Uⱼ)`, where the minors, divided by `xᵢ` and `xⱼ` to make
them functions rather than expressions in the homogeneous coordinates, are
regular functions on `X`. Being closed is local, so that suffices; and the
agreement locus then contains a dense set and is closed, hence is everything.

The target has to be quasi-projective and not an arbitrary `Variety`. This is
not laziness: the abstract structure imposes no separation axiom, and the line
with a doubled origin satisfies it while failing the lemma. Every variety in
Hartshorne's sense — affine, quasi-affine, projective, quasi-projective — is
quasi-projective, so nothing in the source is lost.

## Main results

* `Hartshorne.chartCoord_mem_regular`
* `Hartshorne.eq_of_eqOn_isOpen_hom`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

universe u v

variable {k : Type u} [Field k] {σ : Type v} {Y : Set (ProjectiveSpace k σ)}

/-- The part of `Y` lying in the standard chart `Uᵢ`, as an open subset. -/
def chartOpen (Y : Set (ProjectiveSpace k σ)) (i : σ) : Opens ↥Y where
  carrier := {y : ↥Y | (y : ProjectiveSpace k σ) ∈ standardChart i}
  is_open' := (isOpen_standardChart i).preimage continuous_subtype_val

@[simp]
theorem mem_chartOpen {i : σ} {y : ↥Y} :
    y ∈ chartOpen Y i ↔ (y : ProjectiveSpace k σ) ∈ standardChart i := Iff.rfl

/-- The same open set, read on the variety rather than on the subtype. The two
carriers are definitionally equal; naming the reading keeps `Opens.comap` from
having to see through the definition. -/
noncomputable def chartOpens (hY : IsQuasiProjVariety Y) (i : σ) :
    Opens (Variety.ofQuasiProjective hY).carrier := chartOpen Y i

/-- The chart coordinate `x_l / x_i`, as a function on `Y ∩ Uᵢ`. -/
noncomputable def chartCoord (Y : Set (ProjectiveSpace k σ)) (i l : σ) : chartOpen Y i → k :=
  fun y => ((y : ↥Y) : ProjectiveSpace k σ).rep l / ((y : ↥Y) : ProjectiveSpace k σ).rep i

/-- **The chart coordinates are regular.**

`x_l` and `xᵢ` are homogeneous of the same degree, and the denominator is nowhere
zero on the chart, so the ratio is regular with a single global representation. -/
theorem chartCoord_mem_regular (hY : IsQuasiProjVariety Y) (i l : σ) :
    chartCoord Y i l ∈ (Variety.ofQuasiProjective hY).regular (chartOpen Y i) := by
  intro z
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, X l, X i,
    isHomogeneous_X _ _, isHomogeneous_X _ _, fun x _ => ?_, fun x _ => ?_⟩
  · simpa using rep_ne_zero_of_mem_standardChart x.2
  · simp [chartCoord, projOpenIota]

variable {X : Variety.{u, max u v} k} {hY : IsQuasiProjVariety Y}

/-- The open set where `φ` lands in the chart `Uᵢ` and `ψ` in the chart `Uⱼ`.
These cover `X` as `i` and `j` range, because the charts cover `ℙⁿ`. -/
noncomputable def agreeChart (φ ψ : VarietyHom X (Variety.ofQuasiProjective hY)) (i j : σ) :
    Opens X.carrier :=
  Opens.comap ⟨φ.toFun, φ.continuous_toFun⟩ (chartOpens hY i) ⊓
    Opens.comap ⟨ψ.toFun, ψ.continuous_toFun⟩ (chartOpens hY j)

/-- A chart coordinate of a morphism, as a function on the carrier. It is only
meaningful, and only regular, where the image lies in the chart. -/
noncomputable def coordOf (φ : VarietyHom X (Variety.ofQuasiProjective hY)) (i l : σ)
    (z : X.carrier) : k :=
  (φ z).1.rep l / (φ z).1.rep i

/-- And it is regular on `W_{ij}`, being the pullback of a regular function
along a morphism, restricted. -/
theorem coordOf_mem_regular (φ ψ : VarietyHom X (Variety.ofQuasiProjective hY)) (i j l : σ) :
    (fun z : agreeChart φ ψ i j => coordOf φ i l z.1)
      ∈ X.regular (agreeChart φ ψ i j) :=
  X.regular_restrict (V := agreeChart φ ψ i j) inf_le_left
    (φ.regular_comp (chartOpens hY i) (chartCoord Y i l) (chartCoord_mem_regular hY i l))

/-- The same for `ψ`, in its own chart. -/
theorem coordOf_mem_regular' (φ ψ : VarietyHom X (Variety.ofQuasiProjective hY)) (i j m : σ) :
    (fun z : agreeChart φ ψ i j => coordOf ψ j m z.1)
      ∈ X.regular (agreeChart φ ψ i j) :=
  X.regular_restrict (V := agreeChart φ ψ i j) inf_le_right
    (ψ.regular_comp (chartOpens hY j) (chartCoord Y j m) (chartCoord_mem_regular hY j m))

/-- **The agreement locus of two morphisms is closed.**

On `W_{ij}` it is the zero set of the regular function `a_l b_m − a_m b_l`, the
minor normalised by the two chosen charts. Being closed is a local property, and
the `W_{ij}` cover `X` because the charts cover `ℙⁿ`. -/
theorem isClosed_eqLocus_hom (φ ψ : VarietyHom X (Variety.ofQuasiProjective hY)) :
    IsClosed {z : X.carrier | φ z = ψ z} := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z₀ hz₀
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hz₀
  -- Charts containing the two images.
  obtain ⟨i, hi⟩ : ∃ i, (φ z₀).1.rep i ≠ 0 :=
    Function.ne_iff.1 (Projectivization.rep_nonzero _)
  obtain ⟨j, hj⟩ : ∃ j, (ψ z₀).1.rep j ≠ 0 :=
    Function.ne_iff.1 (Projectivization.rep_nonzero _)
  have hz₀W : z₀ ∈ agreeChart φ ψ i j :=
    ⟨mem_standardChart_iff.2 hi, mem_standardChart_iff.2 hj⟩
  -- Some minor is nonzero, since the two points differ.
  obtain ⟨l, m, hlm⟩ : ∃ l m, (φ z₀).1.rep l * (ψ z₀).1.rep m
      ≠ (φ z₀).1.rep m * (ψ z₀).1.rep l := by
    by_contra hc
    push_neg at hc
    exact hz₀ (Subtype.ext (eq_of_minors_eq_zero hi fun l m => hc l m))
  -- The normalised minor, as a regular function on `W_{ij}`.
  set W := agreeChart φ ψ i j with hW
  set F : W → k := fun z => coordOf φ i l z.1 * coordOf ψ j m z.1
    - coordOf φ i m z.1 * coordOf ψ j l z.1 with hF
  have hFreg : F ∈ X.regular W :=
    sub_mem (mul_mem (coordOf_mem_regular φ ψ i j l) (coordOf_mem_regular' φ ψ i j m))
      (mul_mem (coordOf_mem_regular φ ψ i j m) (coordOf_mem_regular' φ ψ i j l))
  -- It vanishes exactly where the minor does.
  have hFzero : ∀ z : W, F z = 0 ↔
      (φ z.1).1.rep l * (ψ z.1).1.rep m = (φ z.1).1.rep m * (ψ z.1).1.rep l := fun z =>
    div_minor_eq_zero_iff (rep_ne_zero_of_mem_standardChart z.2.1)
      (rep_ne_zero_of_mem_standardChart z.2.2)
  have hFne : F ⟨z₀, hz₀W⟩ ≠ 0 := fun h => hlm ((hFzero _).1 h)
  -- Its nonvanishing locus is an open neighbourhood inside the complement.
  refine ⟨Subtype.val '' {z : W | F z ≠ 0}, ?_, ?_, ⟨⟨z₀, hz₀W⟩, hFne, rfl⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    intro heq
    exact hz ((hFzero z).2 (minors_eq_zero_of_eq (congrArg Subtype.val heq) l m))
  · refine W.isOpen.isOpenMap_subtype_val _ ?_
    have hset : {z : W | F z ≠ 0} = {z : W | F z = 0}ᶜ := rfl
    rw [hset]
    exact (X.isClosed_zeroLocus hFreg).isOpen_compl

/-- **Lemma 4.1**: two morphisms into a quasi-projective variety that agree on a
nonempty open subset agree everywhere. -/
theorem eq_of_eqOn_isOpen_hom (φ ψ : VarietyHom X (Variety.ofQuasiProjective hY))
    {U : Set X.carrier} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hU : ∀ z ∈ U, φ z = ψ z) (z : X.carrier) : φ z = ψ z := by
  have hsub : U ⊆ {z : X.carrier | φ z = ψ z} := hU
  have hcl := (isClosed_eqLocus_hom φ ψ).closure_subset_iff.2 hsub
  exact hcl ((Variety.dense_of_isOpen_of_nonempty hUo hUne).closure_eq ▸ Set.mem_univ z)

end Hartshorne
