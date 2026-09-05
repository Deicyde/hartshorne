/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.LocalRingStructure
import Hartshorne.Morphism.PointsMaximal
import Mathlib.RingTheory.Ideal.Height

/-!
# Theorem 3.2(c): the local ring is a localisation

Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.2(c) (p. 17).

For an affine variety `Y` and a point `P`, `𝒪_P ≅ A(Y)_{𝔪_P}`.

The map is forced: a polynomial function has a germ at `P`, and a polynomial
not vanishing at `P` has an invertible germ, so `A(Y) → 𝒪_P` inverts everything
outside `𝔪_P` and factors through the localisation.

Surjectivity is the definition of regular read backwards. A germ at `P` is
`g/h` on some neighbourhood with `h(P) ≠ 0`, and that datum *is* an element of
`A(Y)_{𝔪_P}`. Injectivity is easier here than Hartshorne's phrasing suggests:
because a germ is an equivalence class for "agree on the whole overlap" rather
than "agree near `P`", a global function with zero germ is zero on all of `Y` on
the nose, with no appeal to the identity principle.

Half of the dimension clause comes free: Mathlib computes the dimension of a
localisation at a prime as that prime's height, so `dim 𝒪_P = height 𝔪_P`. What
is still missing is `height 𝔪_P = dim Y`, which needs the dimension formula, the
second clause of Theorem 1.8A.

## Main definitions

* `Hartshorne.coordToLocal`, `Hartshorne.localizationEquivLocalRing`

## Main results

* `Hartshorne.localizationToLocal_surjective`
* `Hartshorne.ringKrullDim_localRingAt`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)}

instance isPrime_maximalIdealAt (P : Y) : (maximalIdealAt Y P).IsPrime :=
  (maximalIdealAt_isMaximal P).isPrime

variable (hY : IsIrreducible Y)

/-- A polynomial, as a germ at `P`: it is regular on all of `Y`. -/
noncomputable def polyGerm (P : Y) (p : MvPolynomial σ k) : GermRep Y P :=
  globalToGermRep P (polynomialToRegular Y p) (isRegular_polynomialToRegular p)

@[simp]
theorem polyGerm_toFun (P : Y) (p : MvPolynomial σ k) (x : (polyGerm P p).U) :
    (polyGerm P p).toFun x = eval (x.1 : σ → k) p :=
  rfl

/-- Polynomials, as germs at `P`, form a `k`-algebra map. -/
noncomputable def polyToLocal (P : Y) : MvPolynomial σ k →ₐ[k] LocalRingAt hY P where
  toFun p := Quotient.mk _ (polyGerm P p)
  map_one' := Quotient.sound fun _ _ _ => by simp
  map_mul' _ _ := Quotient.sound fun _ _ _ => by simp
  map_zero' := Quotient.sound fun _ _ _ => by simp
  map_add' _ _ := Quotient.sound fun _ _ _ => by simp
  commutes' _ := Quotient.sound fun _ _ _ => by simp

/-- **The map `A(Y) → 𝒪_P`**: a polynomial class, taken as a germ at `P`. It is
well defined because a polynomial vanishing on `Y` has zero germ. -/
noncomputable def coordToLocal (P : Y) : coordinateRing Y →ₐ[k] LocalRingAt hY P :=
  Ideal.Quotient.liftₐ _ (polyToLocal hY P) fun p hp =>
    Quotient.sound fun x _ _ => by simpa using hp x.1 x.2

@[simp]
theorem coordToLocal_mk (P : Y) (p : MvPolynomial σ k) :
    coordToLocal hY P (Ideal.Quotient.mk _ p) = Quotient.mk _ (polyGerm P p) :=
  rfl

/-- Evaluating the germ of a polynomial function at `P` gives its value. -/
@[simp]
theorem evalAtPoint_coordToLocal (P : Y) (a : coordinateRing Y) :
    evalAtPoint (coordToLocal hY P a) = evalAt Y P a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- A function not vanishing at `P` has an invertible germ. This is what makes
`A(Y) → 𝒪_P` factor through the localisation at `𝔪_P`. -/
theorem isUnit_coordToLocal (P : Y) {a : coordinateRing Y}
    (ha : a ∈ (maximalIdealAt Y P).primeCompl) : IsUnit (coordToLocal hY P a) :=
  (isUnit_iff_evalAtPoint_ne_zero _).2 (by
    rw [evalAtPoint_coordToLocal]
    exact fun h => ha (mem_maximalIdealAt.2 h))

/-- A polynomial function with zero germ at `P` is zero on all of `Y`.

Hartshorne's identification is "agree on the whole overlap", and both germs here
are defined on all of `Y`, so this needs no identity principle. -/
theorem coordToLocal_injective (P : Y) : Function.Injective (coordToLocal hY P) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hrel : (polyGerm P p).Rel (GermRep.const P 0) := Quotient.exact ha
  rw [Ideal.Quotient.eq_zero_iff_mem]
  intro x hx
  exact hrel ⟨x, hx⟩ (Set.mem_univ _) (Set.mem_univ _)

/-- The map out of the localisation, by its universal property. -/
noncomputable def localizationToLocal (P : Y) :
    Localization.AtPrime (maximalIdealAt Y P) →+* LocalRingAt hY P :=
  IsLocalization.lift (M := (maximalIdealAt Y P).primeCompl)
    (g := (coordToLocal hY P).toRingHom) fun y => isUnit_coordToLocal hY P y.2

theorem localizationToLocal_mk' (P : Y) (a : coordinateRing Y)
    (s : (maximalIdealAt Y P).primeCompl) (v : LocalRingAt hY P) :
    localizationToLocal hY P (IsLocalization.mk' _ a s) = v
      ↔ coordToLocal hY P a = coordToLocal hY P s * v :=
  IsLocalization.lift_mk'_spec _ _ _ _

theorem localizationToLocal_injective (P : Y) :
    Function.Injective (localizationToLocal hY P) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (maximalIdealAt Y P).primeCompl z
  rw [localizationToLocal_mk', mul_zero] at hz
  have ha : a = 0 := coordToLocal_injective hY P (by rw [hz, map_zero])
  show IsLocalization.mk' (Localization.AtPrime (maximalIdealAt Y P)) a s = 0
  rw [ha, IsLocalization.mk'_zero]

/-- **Surjectivity**: a germ at `P` is a quotient `g/h` with `h(P) ≠ 0` on some
neighbourhood, and that datum is an element of `A(Y)_{𝔪_P}`. -/
theorem localizationToLocal_surjective (P : Y) :
    Function.Surjective (localizationToLocal hY P) := by
  intro x
  obtain ⟨r, rfl⟩ := Quotient.exists_rep x
  obtain ⟨W, hW, hPW, g, h, hne, he⟩ := r.isRegular ⟨P, r.mem_U⟩
  -- `W` is cut out of `Y` by an open set.
  rw [isOpen_induced_iff] at hW
  obtain ⟨O, hO, rfl⟩ := hW
  have hden : (Ideal.Quotient.mk _ h : coordinateRing Y) ∈ (maximalIdealAt Y P).primeCompl := by
    intro hmem
    exact hne ⟨P, r.mem_U⟩ hPW (by simpa using mem_maximalIdealAt.1 hmem)
  refine ⟨IsLocalization.mk' _ (Ideal.Quotient.mk _ g) ⟨_, hden⟩, ?_⟩
  refine (localizationToLocal_mk' hY P _ _ _).2 ?_
  -- Both sides are germs agreeing on `O ∩ r.U`, a neighbourhood of `P`.
  refine Quotient.sound ((GermRep.rel_iff_eventually hY _ _).2
    ⟨O ∩ r.U, hO.inter r.isOpen_U, ⟨hPW, r.mem_U⟩, fun y hy _ hs => ?_⟩)
  have hyW : (⟨y, hs.2⟩ : r.U) ∈ Subtype.val ⁻¹' O := hy.1
  have hy0 := hne ⟨y, hs.2⟩ hyW
  have hyv := he ⟨y, hs.2⟩ hyW
  simp only [GermRep.mul_toFun, polyGerm_toFun]
  rw [hyv, mul_div_cancel₀ _ hy0]

/-- **Theorem 3.2(c)**, the localisation clause: `A(Y)_{𝔪_P} ≅ 𝒪_{P,Y}`. -/
noncomputable def localizationEquivLocalRing (P : Y) :
    Localization.AtPrime (maximalIdealAt Y P) ≃+* LocalRingAt hY P :=
  RingEquiv.ofBijective (localizationToLocal hY P)
    ⟨localizationToLocal_injective hY P, localizationToLocal_surjective hY P⟩

/-- `dim 𝒪_P = height 𝔪_P`.

Free once the local ring is identified with a localisation: Mathlib computes the
dimension of a localisation at a prime as that prime's height. The rest of
Theorem 3.2(c), `height 𝔪_P = dim Y`, is what still needs the dimension
formula. -/
theorem ringKrullDim_localRingAt (P : Y) :
    ringKrullDim (LocalRingAt hY P) = (maximalIdealAt Y P).height := by
  rw [← ringKrullDim_eq_of_ringEquiv (localizationEquivLocalRing hY P)]
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (maximalIdealAt Y P)
    (Localization.AtPrime (maximalIdealAt Y P))

end Hartshorne
