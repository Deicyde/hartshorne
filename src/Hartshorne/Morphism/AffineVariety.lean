/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.Variety

/-!
# Quasi-affine varieties are varieties

Hartshorne, *Algebraic Geometry*, I.3, the definition on p. 15.

This discharges the first of the four constructions the `Variety` structure
demands: a quasi-affine variety, with its regular functions, satisfies the
structure.

Parametrising regularity by a map to affine space rather than by a subtype pays
off here. An open subset of `↥Y` maps to `𝔸ⁿ` by a composite of two coercions,
and `IsRegularVia` takes that composite directly, so nothing has to be
transported.

## Main definitions

* `Hartshorne.regularSubalgebra`
* `Hartshorne.Variety.ofQuasiAffine`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*}
variable {A : Type*} [TopologicalSpace A] {ι : A → (σ → k)}

/-- A constant function is regular: take the whole space, numerator `C c` and
denominator `1`. -/
theorem isRegularVia_const (ι : A → (σ → k)) (c : k) :
    IsRegularVia ι (fun _ => c) := fun _ =>
  ⟨Set.univ, isOpen_univ, Set.mem_univ _, C c, 1, by simp, by simp⟩

/-- A polynomial in the coordinates is regular: denominator `1`. -/
theorem isRegularVia_eval (ι : A → (σ → k)) (p : MvPolynomial σ k) :
    IsRegularVia ι (fun x => eval (ι x) p) := fun _ =>
  ⟨Set.univ, isOpen_univ, Set.mem_univ _, p, 1, by simp, by simp⟩

/-- Sums of regular functions are regular: put the two quotients over a common
denominator on the intersection of their neighbourhoods. -/
theorem IsRegularVia.add {f g : A → k} (hf : IsRegularVia ι f)
    (hg : IsRegularVia ι g) : IsRegularVia ι (f + g) := by
  intro P
  obtain ⟨U₁, hU₁, hP₁, g₁, h₁, hne₁, he₁⟩ := hf P
  obtain ⟨U₂, hU₂, hP₂, g₂, h₂, hne₂, he₂⟩ := hg P
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hP₁, hP₂⟩, g₁ * h₂ + g₂ * h₁, h₁ * h₂,
    fun x hx => ?_, fun x hx => ?_⟩
  · simpa using mul_ne_zero (hne₁ x hx.1) (hne₂ x hx.2)
  · have e₁ := hne₁ x hx.1
    have e₂ := hne₂ x hx.2
    rw [Pi.add_apply, he₁ x hx.1, he₂ x hx.2]
    simp only [map_add, map_mul]
    field_simp

/-- Products of regular functions are regular. -/
theorem IsRegularVia.mul {f g : A → k} (hf : IsRegularVia ι f)
    (hg : IsRegularVia ι g) : IsRegularVia ι (f * g) := by
  intro P
  obtain ⟨U₁, hU₁, hP₁, g₁, h₁, hne₁, he₁⟩ := hf P
  obtain ⟨U₂, hU₂, hP₂, g₂, h₂, hne₂, he₂⟩ := hg P
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hP₁, hP₂⟩, g₁ * g₂, h₁ * h₂,
    fun x hx => ?_, fun x hx => ?_⟩
  · simpa using mul_ne_zero (hne₁ x hx.1) (hne₂ x hx.2)
  · have e₁ := hne₁ x hx.1
    have e₂ := hne₂ x hx.2
    rw [Pi.mul_apply, he₁ x hx.1, he₂ x hx.2]
    simp only [map_mul]
    field_simp

/-- Negatives of regular functions are regular: negate the numerator. -/
theorem IsRegularVia.neg {f : A → k} (hf : IsRegularVia ι f) :
    IsRegularVia ι (-f) := by
  intro P
  obtain ⟨U, hU, hP, g, h, hne, he⟩ := hf P
  exact ⟨U, hU, hP, -g, h, hne, fun x hx => by
    rw [Pi.neg_apply, he x hx, map_neg, neg_div]⟩

/-- A nowhere-zero regular function has a regular inverse: swap numerator and
denominator.

The new denominator is the old numerator, and it is nonvanishing precisely
because `f` is: `f = g/h` and `f ≠ 0` force `g ≠ 0`. -/
theorem IsRegularVia.inv {f : A → k} (hf : IsRegularVia ι f) (hne : ∀ x, f x ≠ 0) :
    IsRegularVia ι f⁻¹ := by
  intro P
  obtain ⟨U, hU, hP, g, h, hh, he⟩ := hf P
  refine ⟨U, hU, hP, h, g, fun x hx hg => hne x ?_, fun x hx => ?_⟩
  · rw [he x hx, hg, zero_div]
  · rw [Pi.inv_apply, he x hx, inv_div]

variable {Y : Set (σ → k)}

/-- The map to affine space attached to an open subset of `Y`: two coercions
composed. -/
abbrev openIota (U : Opens Y) : U → (σ → k) :=
  fun x => Subtype.val (Subtype.val x)

/-- The regular functions on an open subset of a subset of affine space, as a
`k`-subalgebra. -/
noncomputable def regularSubalgebra (U : Opens Y) :
    Subalgebra k (U → k) where
  carrier := {f | IsRegularVia (openIota U) f}
  mul_mem' hf hg := IsRegularVia.mul hf hg
  one_mem' := isRegularVia_const _ 1
  add_mem' hf hg := IsRegularVia.add hf hg
  zero_mem' := isRegularVia_const _ 0
  algebraMap_mem' c := isRegularVia_const _ c

@[simp]
theorem mem_regularSubalgebra {U : Opens Y} {f : U → k} :
    f ∈ regularSubalgebra U ↔ IsRegularVia (openIota U) f :=
  Iff.rfl

set_option maxHeartbeats 1000000 in
/-- A quasi-affine variety, viewed as a `Variety`.

This is the first of Hartshorne's four cases. Discharging it is the cost the
bundled representation charges, and it is what makes statements quantified over
an arbitrary variety apply to quasi-affine ones. -/
noncomputable def Variety.ofQuasiAffine (hY : IsQuasiAffineVariety Y) : Variety k where
  carrier := Y
  irreducible := by
    have hne : Nonempty Y := hY.1.to_subtype
    have hpre : PreirreducibleSpace Y :=
      isPreirreducible_iff_preirreducibleSpace.1 hY.isIrreducible.2
    exact { toPreirreducibleSpace := hpre, toNonempty := hne }
  regular := fun U => regularSubalgebra U
  regular_restrict {U V} hUV {f} hf := by
    intro P
    -- The inclusion `↥V → ↥U` commutes with the maps to affine space, so a
    -- representing quotient upstairs pulls back unchanged.
    obtain ⟨W, hW, hPW, g, h, hne, he⟩ := hf ⟨P.1, hUV P.2⟩
    refine ⟨(fun x : V => (⟨x.1, hUV x.2⟩ : U)) ⁻¹' W, ?_, hPW, g, h,
      fun x hx => hne _ hx, fun x hx => he _ hx⟩
    exact hW.preimage (Continuous.subtype_mk continuous_subtype_val _)
  isClosed_zeroLocus {U} {f} hf := by
    -- Lemma 3.1 applied to the pair `(f, 0)`.
    have := isClosed_eqLocusVia (ι := openIota U) (by fun_prop) hf
      (isRegularVia_const (openIota U) 0)
    simpa using this
  regular_div {U} {f g} hf hg hgne := by
    have : (fun x : U => f x / g x) = f * g⁻¹ := by
      funext x; rw [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    rw [this]
    exact IsRegularVia.mul hf (IsRegularVia.inv hg hgne)
  regular_of_locally {U} {f} hloc := by
    intro P
    obtain ⟨V, hVU, hPV, hV⟩ := hloc P
    -- The local datum at `P`, read inside `V`.
    obtain ⟨W, hW, hPW, g, h, hne, he⟩ := hV ⟨P.1, hPV⟩
    -- `W` is open in `↥V`, so it is cut out of the carrier by an open set,
    -- and the same set cuts out a neighbourhood of `P` inside `↥U`.
    rw [isOpen_induced_iff] at hW
    obtain ⟨O, hO, rfl⟩ := hW
    refine ⟨Subtype.val ⁻¹' (O ∩ (V : Set Y)),
      (hO.inter V.isOpen).preimage continuous_subtype_val, ⟨hPW, hPV⟩, g, h,
      fun x hx => hne ⟨x.1, hx.2⟩ hx.1, fun x hx => he ⟨x.1, hx.2⟩ hx.1⟩

end Hartshorne
