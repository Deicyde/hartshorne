/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.MorphismToAffine
import Hartshorne.Morphism.CoordinateRingIso

/-!
# Proposition 3.5: morphisms into an affine variety

Hartshorne, *Algebraic Geometry*, I.3, Proposition 3.5 (p. 19).

For any variety `X` and any affine variety `Y`, there is a bijection

`Hom(X, Y) ≃ Hom_{k-alg}(A(Y), 𝒪(X))`.

Forward, a morphism pulls polynomial functions on `Y` back to regular functions
on `X`. Backward, a `k`-algebra map `h` determines a point of `𝔸ⁿ` for each
`x ∈ X`, coordinate by coordinate, by `ψ(x)ᵢ = h(x̄ᵢ)(x)`. That point lies in `Y`
because `f(ψ(x)) = h(f̄)(x)` for every polynomial `f`, which vanishes when
`f ∈ I(Y)`; and `ψ` is a morphism by Lemma 3.6, since its coordinates are `h(x̄ᵢ)`
and those are regular by construction.

## A shortcut through the statement

Hartshorne phrases the forward map as "pull back regular functions, then use
`𝒪(Y) ≅ A(Y)`", so the proposition reads as depending on Theorem 3.2(a). It does
not. Precomposing with the map `A(Y) → 𝒪(Y)` gives the same thing, and the
bijection never needs that map to be injective or surjective. Nothing here uses
an algebraically closed field either.

The one identity doing the work is `f(ψ(x)) = h(f̄)(x)`, and it is proved the way
such things should be: both sides are `k`-algebra maps out of `MvPolynomial σ k`
in `f`, and they agree on the variables.

## Main definitions

* `Hartshorne.homToAlgHom`, `Hartshorne.algHomToHom`
* `Hartshorne.homEquivAlgHom`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

universe u

variable {k : Type u} [Field k] {σ : Type*} {Y : Set (σ → k)}

variable {X : Variety k}

/-- The forward map: a morphism `X → Y` pulls a polynomial function on `Y` back
to a regular function on `X`. -/
noncomputable def homToAlgHom (hY : IsAffineVariety Y)
    (ρ : VarietyHom X (Variety.ofQuasiAffine hY.isQuasiAffineVariety)) :
    coordinateRing Y →ₐ[k] X.regular ⊤ :=
  AlgHom.codRestrict
    ((compAlgHom fun z : (⊤ : Opens X.carrier) => (ρ z.1 : Y)).comp (coordinateToRegular Y))
    (X.regular ⊤)
    fun a => by
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ρ.regular_comp ⊤ _ (isRegularVia_eval (openIota ⊤) p)

@[simp]
theorem homToAlgHom_val (hY : IsAffineVariety Y)
    (ρ : VarietyHom X (Variety.ofQuasiAffine hY.isQuasiAffineVariety))
    (a : coordinateRing Y) (z : (⊤ : Opens X.carrier)) :
    (homToAlgHom hY ρ a).val z = coordinateToRegular Y a (ρ z.1) :=
  rfl

/-- The point of `𝔸ⁿ` attached to a `k`-algebra map, coordinate by coordinate.
-/
noncomputable def algHomToFun (h : coordinateRing Y →ₐ[k] X.regular ⊤)
    (x : X.carrier) : σ → k :=
  fun i => (h (Ideal.Quotient.mk _ (MvPolynomial.X i))).val ⟨x, trivial⟩

/-- Evaluating a polynomial at that point is applying `h` to its class.

Both sides are `k`-algebra maps out of `MvPolynomial σ k` and agree on the
variables. -/
theorem eval_algHomToFun (h : coordinateRing Y →ₐ[k] X.regular ⊤) (x : X.carrier)
    (p : MvPolynomial σ k) :
    eval (algHomToFun h x) p = (h (Ideal.Quotient.mk _ p)).val ⟨x, trivial⟩ := by
  have key : ((Pi.evalAlgHom k (fun _ : (⊤ : Opens X.carrier) => k) ⟨x, trivial⟩).comp
      ((X.regular ⊤).val.comp (h.comp (Ideal.Quotient.mkₐ k (vanishingIdeal k Y)))))
      = aeval (algHomToFun h x) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [algHomToFun]
  exact (congrArg (fun φ => φ p) key).symm

/-- The point lands in `Y`: every `f ∈ I(Y)` has class `0`, so it vanishes
there. -/
theorem algHomToFun_mem (hY : IsAffineVariety Y) (h : coordinateRing Y →ₐ[k] X.regular ⊤)
    (x : X.carrier) : algHomToFun h x ∈ Y := by
  have hz : algHomToFun h x ∈ zeroLocus k (vanishingIdeal k Y) := by
    intro p hp
    show eval (algHomToFun h x) p = 0
    rw [eval_algHomToFun, Ideal.Quotient.eq_zero_iff_mem.2 hp]
    simp
  rwa [IsAlgebraicSet.zeroLocus_vanishingIdeal (IsAffineVariety.isAlgebraicSet hY)] at hz

/-- The coordinates of that point are regular, being the values of `h`. -/
theorem isGlobalRegular_algHomToFun (h : coordinateRing Y →ₐ[k] X.regular ⊤) (i : σ) :
    X.IsGlobalRegular fun x => algHomToFun h x i :=
  (h (Ideal.Quotient.mk _ (MvPolynomial.X i))).2

/-- The inverse map: a `k`-algebra map `A(Y) → 𝒪(X)` is a morphism `X → Y`.

Being a morphism is Lemma 3.6, since the coordinates are exactly the values of
`h` and those are regular. -/
noncomputable def algHomToHom (hY : IsAffineVariety Y)
    (h : coordinateRing Y →ₐ[k] X.regular ⊤) :
    VarietyHom X (Variety.ofQuasiAffine hY.isQuasiAffineVariety) :=
  let φ : X.carrier → Y := fun x => ⟨algHomToFun h x, algHomToFun_mem hY h x⟩
  have hco : ∀ i, X.IsGlobalRegular fun x => (φ x : σ → k) i := isGlobalRegular_algHomToFun h
  have hcont : Continuous φ :=
    (Variety.continuous_of_coords_regular _ hco).subtype_mk fun x => (φ x).2
  ⟨φ, hcont, fun V _f hf => regular_comp_of_coords_regular φ hcont hco V hf⟩

@[simp]
theorem algHomToHom_apply (hY : IsAffineVariety Y)
    (h : coordinateRing Y →ₐ[k] X.regular ⊤) (x : X.carrier) :
    (((algHomToHom hY h).toFun x).1 : σ → k) = algHomToFun h x :=
  rfl

/-- **Proposition 3.5**: morphisms `X → Y` into an affine variety correspond to
`k`-algebra maps `A(Y) → 𝒪(X)`. -/
noncomputable def homEquivAlgHom (hY : IsAffineVariety Y) :
    VarietyHom X (Variety.ofQuasiAffine hY.isQuasiAffineVariety)
      ≃ (coordinateRing Y →ₐ[k] X.regular ⊤) where
  toFun := homToAlgHom hY
  invFun := algHomToHom hY
  left_inv ρ := by
    refine VarietyHom.ext (funext fun x => Subtype.ext (funext fun i => ?_))
    show algHomToFun (homToAlgHom hY ρ) x i = _
    simp only [algHomToFun, homToAlgHom_val, coordinateToRegular_mk]
    exact eval_X i
  right_inv h := by
    refine AlgHom.ext fun a => Subtype.ext (funext fun z => ?_)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    show eval (algHomToFun h z.1) p = _
    exact eval_algHomToFun h z.1 p

end Hartshorne
