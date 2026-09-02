/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.AffineVariety

/-!
# The ring of regular functions

Hartshorne, *Algebraic Geometry*, I.3, the definition of `𝒪(Y)` on p. 16.

`𝒪(Y)` is the `k`-algebra of regular functions on `Y`. For a quasi-affine `Y`
this is a subalgebra of all functions `Y → k`, and the closure lemmas are the
ones already used to build the subalgebra on each open subset.

This is stated directly for a subset of affine space rather than through the
`Variety` structure. Theorem 3.2, the main result of the section, is entirely
about affine varieties, and going through the bundled representation costs an
abstraction that is currently blocked on the projective side; see the roadmap
article for `Varieties`.

## Main definitions

* `Hartshorne.globalRegular`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- Hartshorne's `𝒪(Y)`: the `k`-algebra of regular functions on `Y`. -/
noncomputable def globalRegular (Y : Set (σ → k)) : Subalgebra k (Y → k) where
  carrier := {f | IsRegular f}
  mul_mem' hf hg := IsRegularVia.mul hf hg
  one_mem' := isRegularVia_const _ 1
  add_mem' hf hg := IsRegularVia.add hf hg
  zero_mem' := isRegularVia_const _ 0
  algebraMap_mem' c := isRegularVia_const _ c

@[simp]
theorem mem_globalRegular {Y : Set (σ → k)} {f : Y → k} :
    f ∈ globalRegular Y ↔ IsRegular f :=
  Iff.rfl

/-- Polynomials restrict to regular functions: the map `A → 𝒪(Y)` that
Theorem 3.2 will show is surjective with kernel `I(Y)`. -/
noncomputable def polynomialToRegular (Y : Set (σ → k)) :
    MvPolynomial σ k →ₐ[k] (Y → k) where
  toFun p := fun x => eval (x : σ → k) p
  map_one' := by funext x; simp
  map_mul' p q := by funext x; simp
  map_zero' := by funext x; simp
  map_add' p q := by funext x; simp
  commutes' c := by funext x; simp

@[simp]
theorem polynomialToRegular_apply {Y : Set (σ → k)} (p : MvPolynomial σ k) (x : Y) :
    polynomialToRegular Y p x = eval (x : σ → k) p :=
  rfl

/-- A polynomial function is regular: take the whole space, with denominator
`1`. -/
theorem isRegular_polynomialToRegular {Y : Set (σ → k)} (p : MvPolynomial σ k) :
    IsRegular (polynomialToRegular Y p) := fun _ =>
  ⟨Set.univ, isOpen_univ, Set.mem_univ _, p, 1, by simp, by simp⟩

/-- The restriction map lands in `𝒪(Y)`, giving the `k`-algebra homomorphism
`A(Y) → 𝒪(Y)` of Theorem 3.2 before passing to the quotient. -/
theorem polynomialToRegular_mem_globalRegular {Y : Set (σ → k)} (p : MvPolynomial σ k) :
    polynomialToRegular Y p ∈ globalRegular Y :=
  isRegular_polynomialToRegular p

/-- The kernel of `A → 𝒪(Y)` is exactly the vanishing ideal `I(Y)`. This is the
first half of Theorem 3.2(a): the induced map `A(Y) → 𝒪(Y)` is injective. -/
theorem polynomialToRegular_eq_zero_iff {Y : Set (σ → k)} (p : MvPolynomial σ k) :
    polynomialToRegular Y p = 0 ↔ p ∈ vanishingIdeal k Y := by
  constructor
  · intro h x hx
    have := congrFun h ⟨x, hx⟩
    simpa using this
  · intro h
    funext x
    simpa using h x x.2

end Hartshorne
