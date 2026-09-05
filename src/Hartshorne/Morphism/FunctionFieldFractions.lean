/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.FunctionFieldStructure
import Hartshorne.Affine.CoordinateRing
import Hartshorne.Affine.DimensionCoordinateRing
import Hartshorne.Dimension.FgDomain
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Theorem 3.2(d): the function field is the fraction field

Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.2(d) (p. 17).

For an affine variety `Y`, `K(Y)` is the fraction field of `A(Y)`.

Three things have to be checked, and they are the three clauses of
`IsLocalization` at the non-zero-divisors.

A nonzero element of `A(Y)` becomes a unit: it does not vanish identically, so
the open set where it is nonzero is nonempty and its reciprocal is regular
there. Every rational function is a fraction: it is `g/h` on some nonempty open
set by the definition of regular. And the map is injective, so no denominator is
needed to witness an equality.

The middle clause is the one where irreducibility does real work. `h · z = g`
holds *on the open set where the local description was taken*, and Hartshorne's
identification requires agreement on the whole overlap; the identity principle
upgrades one to the other. This is the same step that made the relation
transitive in the first place.

## Main results

* `Hartshorne.RationalRep.rel_of_eqOn`
* `Hartshorne.isFractionRing_functionField`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)}

/-- **The identity principle for rational functions**: two representatives
agreeing on any nonempty open set are equivalent.

Hartshorne's identification asks for agreement on the whole overlap, which is
what makes the relation usable; this is what lets local information supply it.
-/
theorem RationalRep.rel_of_eqOn (hY : IsIrreducible Y) {r s : RationalRep Y}
    {W : Set Y} (hW : IsOpen W) (hWne : W.Nonempty)
    (h : ∀ (x : Y), x ∈ W → ∀ (hr : x ∈ r.U) (hs : x ∈ s.U),
      r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩) : r.Rel s := by
  intro x hr hs
  set V : Set Y := r.U ∩ s.U with hV
  have hVopen : IsOpen V := r.isOpen_U.inter s.isOpen_U
  have hVne : V.Nonempty := inter_nonempty hY r.isOpen_U s.isOpen_U r.nonempty_U s.nonempty_U
  have hfr : IsRegularVia (fun y : V => (y.1 : σ → k)) (fun y : V => r.toFun ⟨y.1, y.2.1⟩) :=
    isRegularVia_restrict (fun _ hy => hy.1) r.isRegular
  have hfs : IsRegularVia (fun y : V => (y.1 : σ → k)) (fun y : V => s.toFun ⟨y.1, y.2.2⟩) :=
    isRegularVia_restrict (fun _ hy => hy.2) s.isRegular
  have hVirr : IsPreirreducible (Set.univ : Set V) := preirreducible_univ_of_isOpen hY hVopen hVne
  have hsub : IsOpen {y : V | (y : Y) ∈ W} := hW.preimage continuous_subtype_val
  have hne : ({y : V | (y : Y) ∈ W}).Nonempty := by
    obtain ⟨z, hzV, hzW⟩ := inter_nonempty hY hVopen hW hVne hWne
    exact ⟨⟨z, hzV⟩, hzW⟩
  have heq : Set.EqOn (fun y : V => r.toFun ⟨y.1, y.2.1⟩) (fun y : V => s.toFun ⟨y.1, y.2.2⟩)
      {y : V | (y : Y) ∈ W} := fun y hy => h y.1 hy y.2.1 y.2.2
  have hall := eq_of_eqOn_isOpen hVirr (by fun_prop) hfr hfs hsub hne heq
  exact congrFun hall ⟨x, ⟨hr, hs⟩⟩

variable (hY : IsIrreducible Y)

/-- A polynomial, as a rational function on all of `Y`. -/
noncomputable def polyRational (p : MvPolynomial σ k) : RationalRep Y where
  U := Set.univ
  isOpen_U := isOpen_univ
  nonempty_U := hY.1.to_subtype.elim fun x => ⟨x, Set.mem_univ x⟩
  toFun := fun x => eval (x.1 : σ → k) p
  isRegular := isRegularVia_eval _ p

@[simp]
theorem polyRational_toFun (p : MvPolynomial σ k) (x : (polyRational hY p).U) :
    (polyRational hY p).toFun x = eval (x.1 : σ → k) p :=
  rfl

/-- Polynomials, as rational functions, form a `k`-algebra map. -/
noncomputable def polyToRational : MvPolynomial σ k →ₐ[k] FunctionField hY where
  toFun p := Quotient.mk _ (polyRational hY p)
  map_one' := Quotient.sound fun _ _ _ => by simp
  map_mul' _ _ := Quotient.sound fun _ _ _ => by simp
  map_zero' := Quotient.sound fun _ _ _ => by simp
  map_add' _ _ := Quotient.sound fun _ _ _ => by simp
  commutes' _ := Quotient.sound fun _ _ _ => by simp

/-- **The map `A(Y) → K(Y)`**: a polynomial class, as a rational function. -/
noncomputable def coordToRational : coordinateRing Y →ₐ[k] FunctionField hY :=
  Ideal.Quotient.liftₐ _ (polyToRational hY) fun p hp =>
    Quotient.sound fun x _ _ => by simpa using hp x.1 x.2

@[simp]
theorem coordToRational_mk (p : MvPolynomial σ k) :
    coordToRational hY (Ideal.Quotient.mk _ p) = Quotient.mk _ (polyRational hY p) :=
  rfl

/-- `A(Y) → K(Y)` is injective: a polynomial function that is zero as a rational
function has domain all of `Y`, so it is zero everywhere. -/
theorem coordToRational_injective : Function.Injective (coordToRational hY) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hrel : (polyRational hY p).Rel (RationalRep.const hY 0) := Quotient.exact ha
  rw [Ideal.Quotient.eq_zero_iff_mem]
  intro x hx
  exact hrel ⟨x, hx⟩ (Set.mem_univ _) (Set.mem_univ _)

namespace RationalRep

/-- The set where a rational function is nonzero. -/
def nonvanishing (r : RationalRep Y) : Set Y :=
  {x | (∀ hx : x ∈ r.U, r.toFun ⟨x, hx⟩ ≠ 0) ∧ x ∈ r.U}

theorem nonvanishing_subset (r : RationalRep Y) : r.nonvanishing ⊆ r.U := fun _ hx => hx.2

theorem nonvanishing_eq_image (r : RationalRep Y) :
    r.nonvanishing = Subtype.val '' {y : r.U | r.toFun y ≠ 0} := by
  ext x
  constructor
  · rintro ⟨hall, hx⟩
    exact ⟨⟨x, hx⟩, hall hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun _ => hy, y.2⟩

theorem isOpen_nonvanishing (r : RationalRep Y) : IsOpen r.nonvanishing := by
  rw [nonvanishing_eq_image]
  refine r.isOpen_U.isOpenMap_subtype_val _ ?_
  have hclosed : IsClosed {y : r.U | r.toFun y = 0} := by
    have := isClosed_eqLocusVia (ι := fun x : r.U => (x.1 : σ → k))
      (by fun_prop) r.isRegular (isRegularVia_const (fun x : r.U => (x.1 : σ → k)) 0)
    simpa using this
  simpa [Set.compl_ofPred] using hclosed.isOpen_compl

/-- A rational function that is not the zero class is nonzero somewhere. -/
theorem nonvanishing_nonempty (hY : IsIrreducible Y) {r : RationalRep Y}
    (h : ¬ r.Rel (const hY 0)) : r.nonvanishing.Nonempty := by
  by_contra hne
  refine h fun x hr _ => ?_
  by_contra hv
  exact hne ⟨x, ⟨fun _ => hv, hr⟩⟩

/-- The reciprocal of a rational function, on the open set where it is
nonzero. -/
noncomputable def inv (r : RationalRep Y) (h : r.nonvanishing.Nonempty) : RationalRep Y where
  U := r.nonvanishing
  isOpen_U := r.isOpen_nonvanishing
  nonempty_U := h
  toFun := fun x => (r.toFun ⟨x.1, x.2.2⟩)⁻¹
  isRegular :=
    (isRegularVia_restrict r.nonvanishing_subset r.isRegular).inv
      fun x => x.2.1 (r.nonvanishing_subset x.2)

@[simp]
theorem inv_toFun (r : RationalRep Y) (h : r.nonvanishing.Nonempty) (x : Y)
    (hx : x ∈ (r.inv h).U) : (r.inv h).toFun ⟨x, hx⟩ = (r.toFun ⟨x, hx.2⟩)⁻¹ :=
  rfl

theorem mul_inv_rel_one (hY : IsIrreducible Y) (r : RationalRep Y)
    (h : r.nonvanishing.Nonempty) : (mul hY r (r.inv h)).Rel (const hY 1) := by
  intro x hx _
  rw [mul_toFun, inv_toFun, const_toFun]
  exact mul_inv_cancel₀ (hx.2.1 hx.2.2)

end RationalRep

/-- The class of a representative, written so that the type `K(Y)` is visible
and its ring structure is found by instance search. -/
def ratClass (hY : IsIrreducible Y) (r : RationalRep Y) : FunctionField hY := Quotient.mk _ r

theorem ratClass_mul (hY : IsIrreducible Y) (r s : RationalRep Y) :
    ratClass hY r * ratClass hY s = ratClass hY (RationalRep.mul hY r s) := rfl

/-- `K(Y)` is an `A(Y)`-algebra, via the map sending a polynomial class to the
rational function it defines. -/
noncomputable instance algebraCoordinateRingFunctionField (hY : IsIrreducible Y) :
    Algebra (coordinateRing Y) (FunctionField hY) :=
  (coordToRational hY).toRingHom.toAlgebra

/-- `k → A(Y) → K(Y)` is a tower, because `A(Y) → K(Y)` is a `k`-algebra map. -/
instance isScalarTower_functionField (hY : IsIrreducible Y) :
    IsScalarTower k (coordinateRing Y) (FunctionField hY) :=
  IsScalarTower.of_algebraMap_eq fun c => ((coordToRational hY).commutes c).symm

/-- A nonzero element of `A(Y)` is invertible in `K(Y)`: it is nonzero on a
nonempty open set, where its reciprocal is regular. -/
theorem isUnit_coordToRational {a : coordinateRing Y} (ha : a ≠ 0) :
    IsUnit (coordToRational hY a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hnr : ¬ (polyRational hY p).Rel (RationalRep.const hY 0) := by
    intro hrel
    refine ha ?_
    rw [Ideal.Quotient.eq_zero_iff_mem]
    intro x hx
    exact hrel ⟨x, hx⟩ (Set.mem_univ _) (Set.mem_univ _)
  have hne := RationalRep.nonvanishing_nonempty hY hnr
  have hmul : ratClass hY (polyRational hY p)
      * ratClass hY ((polyRational hY p).inv hne) = 1 := by
    rw [ratClass_mul]
    exact Quotient.sound (RationalRep.mul_inv_rel_one hY _ hne)
  exact ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

section Fractions

variable [IsDomain (coordinateRing Y)]

/-- **Theorem 3.2(d)**, the fraction field clause: `K(Y)` is the fraction field
of `A(Y)`. -/
theorem isFractionRing_functionField :
    IsFractionRing (coordinateRing Y) (FunctionField hY) := by
  refine (isLocalization_iff _ _).2 ⟨fun s => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · exact isUnit_coordToRational hY (nonZeroDivisors.ne_zero s.2)
  · obtain ⟨r, rfl⟩ := Quotient.exists_rep z
    obtain ⟨P, hP⟩ := r.nonempty_U
    obtain ⟨W, hW, hPW, g, h, hne, he⟩ := r.isRegular ⟨P, hP⟩
    rw [isOpen_induced_iff] at hW
    obtain ⟨O, hO, rfl⟩ := hW
    have hh : (Ideal.Quotient.mk _ h : coordinateRing Y) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      intro hmem
      exact hne ⟨P, hP⟩ hPW (hmem P.1 P.2)
    refine ⟨⟨Ideal.Quotient.mk _ g,
      ⟨Ideal.Quotient.mk _ h, mem_nonZeroDivisors_of_ne_zero hh⟩⟩, ?_⟩
    refine Quotient.sound (RationalRep.rel_of_eqOn hY (W := O ∩ r.U)
      (hO.inter r.isOpen_U) ⟨P, hPW, hP⟩ fun y hy hr _ => ?_)
    have hy0 := hne ⟨y, hr.1⟩ hy.1
    have hyv := he ⟨y, hr.1⟩ hy.1
    simp only [RationalRep.mul_toFun, polyRational_toFun]
    rw [hyv, div_mul_cancel₀ _ hy0]
  · exact ⟨1, by rw [coordToRational_injective hY hxy]⟩

end Fractions

/-- **Theorem 3.2(d)**: the function field of an affine variety has
transcendence degree `dim Y` over `k`.

`K(Y)` is the fraction field of `A(Y)` by the previous result, `dim Y` is
`dim A(Y)` by Proposition 1.7, and Theorem 1.8A(a) says that dimension is the
transcendence degree of the fraction field.

Stated for `Y ⊆ 𝔸ⁿ` with `n` a natural number rather than an arbitrary finite
index type, so that `k`, `A(Y)` and `K(Y)` share a universe; Theorem 1.8A(a)
compares them with a polynomial ring over `k` and needs that. -/
theorem exists_dim_eq_trdeg_functionField [IsAlgClosed k] {n : ℕ} {Z : Set (Fin n → k)}
    (hZ : IsAffineVariety Z) :
    ∃ s : ℕ, dim Z = s ∧ Algebra.trdeg k (FunctionField hZ.isIrreducible) = s := by
  have : IsDomain (coordinateRing Z) := isDomain_coordinateRing hZ
  have : IsFractionRing (coordinateRing Z) (FunctionField hZ.isIrreducible) :=
    isFractionRing_functionField hZ.isIrreducible
  let : Field (FunctionField hZ.isIrreducible) := IsFractionRing.toField (coordinateRing Z)
  obtain ⟨s, hdim, htr⟩ :=
    exists_ringKrullDim_eq_trdeg k (coordinateRing Z) (FunctionField hZ.isIrreducible)
  exact ⟨s, by rw [dim_eq_ringKrullDim_coordinateRing hZ.isAlgebraicSet, hdim], htr⟩

end Hartshorne
