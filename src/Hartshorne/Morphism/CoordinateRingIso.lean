/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.PointsMaximal

/-!
# Theorem 3.2(a): the coordinate ring is the ring of regular functions

Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.2(a) (p. 17).

For an affine variety `Y`, the map `A(Y) → 𝒪(Y)` sending a polynomial class to
the function it defines is an isomorphism of `k`-algebras.

Injectivity is the correspondence of §1: a polynomial defining the zero function
on `Y` lies in `I(Y)`.

## Surjectivity, and why not Hartshorne's route

Hartshorne deduces surjectivity from part (c), writing
`𝒪(Y) = ⋂_P 𝒪_P = ⋂_𝔪 A(Y)_𝔪 = A(Y)` inside `K(Y)`. That needs the local rings,
their identification with localisations, and the outside fact that a domain is
the intersection of its localisations at all maximal ideals.

The route taken here needs none of them. Given a regular `f`, collect the
*denominators*

`𝔞 = {a ∈ A(Y) : a · f is again a polynomial function}`,

which is an ideal. Regularity at `P` gives `f = g/h` near `P` with `h(P) ≠ 0`,
and `h · f` agrees with `g` on that neighbourhood; both are regular on all of
`Y`, so the identity principle upgrades this to agreement everywhere. Hence
`h̄ ∈ 𝔞` and `h̄ ∉ 𝔪_P`. So `𝔞` lies in no maximal ideal — every maximal ideal is
some `𝔪_P` by part (b) — and therefore `𝔞 = A(Y)`. Then `1 ∈ 𝔞`, which says
exactly that `f` is a polynomial function.

Both ingredients are already here: the identity principle, and part (b). The
irreducibility of `Y` is what makes the identity principle available, and it is
the only place it is used.

## Main definitions

* `Hartshorne.coordinateToRegular`, `Hartshorne.denominators`
* `Hartshorne.coordinateRingEquivGlobalRegular`

## Main results

* `Hartshorne.coordinateToRegular_injective`, `Hartshorne.coordinateToRegular_surjective`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)}

/-- The map `α : A(Y) → 𝒪(Y)` of Theorem 3.2: a polynomial class, read as a
function on `Y`. It is well defined because `I(Y)` is exactly the set of
polynomials vanishing on `Y`. -/
noncomputable def coordinateToRegular (Y : Set (σ → k)) :
    coordinateRing Y →ₐ[k] (Y → k) :=
  Ideal.Quotient.liftₐ _ (polynomialToRegular Y)
    fun p hp => (polynomialToRegular_eq_zero_iff p).2 hp

@[simp]
theorem coordinateToRegular_mk (p : MvPolynomial σ k) :
    coordinateToRegular Y (Ideal.Quotient.mk _ p) = polynomialToRegular Y p :=
  rfl

theorem coordinateToRegular_apply (a : coordinateRing Y) (x : Y) :
    coordinateToRegular Y a x = evalAt Y x a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp

/-- Every value of `α` is a regular function: a polynomial function is regular.
-/
theorem coordinateToRegular_mem_globalRegular (a : coordinateRing Y) :
    coordinateToRegular Y a ∈ globalRegular Y := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simpa using isRegular_polynomialToRegular p

/-- **Theorem 3.2(a)**, injectivity. This is Corollary 1.4 through the quotient:
a polynomial defining the zero function on `Y` lies in `I(Y)`. -/
theorem coordinateToRegular_injective : Function.Injective (coordinateToRegular Y) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (polynomialToRegular_eq_zero_iff p).1 (by simpa using ha)

/-- Hartshorne's ideal of denominators of a function `f`: those `a ∈ A(Y)` whose
product with `f` is again a polynomial function.

An ideal rather than merely a set, which is the whole point: it can then be
compared with the maximal ideals. -/
noncomputable def denominators (Y : Set (σ → k)) (f : Y → k) : Ideal (coordinateRing Y) where
  carrier := {a | ∃ b : coordinateRing Y,
    (fun x => coordinateToRegular Y a x * f x) = coordinateToRegular Y b}
  zero_mem' := ⟨0, by funext x; simp⟩
  add_mem' := by
    rintro a₁ a₂ ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩
    refine ⟨b₁ + b₂, ?_⟩
    funext x
    have h₁ := congrFun hb₁ x
    have h₂ := congrFun hb₂ x
    simp only [map_add, Pi.add_apply] at h₁ h₂ ⊢
    rw [add_mul, h₁, h₂]
  smul_mem' := by
    rintro c a ⟨b, hb⟩
    refine ⟨c * b, ?_⟩
    funext x
    have h := congrFun hb x
    simp only [smul_eq_mul, map_mul, Pi.mul_apply] at h ⊢
    rw [mul_assoc, h]

theorem mem_denominators_iff {f : Y → k} {a : coordinateRing Y} :
    a ∈ denominators Y f ↔ ∃ b : coordinateRing Y,
      (fun x => coordinateToRegular Y a x * f x) = coordinateToRegular Y b :=
  Iff.rfl

/-- At every point there is a denominator that does not vanish.

Regularity at `P` writes `f = g/h` near `P` with `h(P) ≠ 0`. Then `h · f` and
`g` are regular on all of `Y` and agree on that neighbourhood, so by the
identity principle they agree everywhere, which is exactly `h̄ ∈ 𝔞`. -/
theorem exists_mem_denominators_evalAt_ne_zero (hY : IsIrreducible Y) {f : Y → k}
    (hf : IsRegular f) (P : Y) :
    ∃ a ∈ denominators Y f, evalAt Y P a ≠ 0 := by
  obtain ⟨U, hU, hPU, g, h, hne, he⟩ := hf P
  refine ⟨Ideal.Quotient.mk _ h, ⟨Ideal.Quotient.mk _ g, ?_⟩, ?_⟩
  · -- The two regular functions `h · f` and `g` agree on `U`.
    have hirr : IsPreirreducible (Set.univ : Set Y) := by
      have : PreirreducibleSpace Y := isPreirreducible_iff_preirreducibleSpace.1 hY.2
      exact PreirreducibleSpace.isPreirreducible_univ
    have hlhs : IsRegular (fun x : Y => polynomialToRegular Y h x * f x) :=
      IsRegularVia.mul (isRegular_polynomialToRegular h) hf
    have hrhs : IsRegular (polynomialToRegular Y g) := isRegular_polynomialToRegular g
    refine eq_of_eqOn_isOpen hirr continuous_subtype_val hlhs hrhs hU ⟨P, hPU⟩ ?_
    intro x hx
    have hx0 := hne x hx
    simp only [coordinateToRegular_mk, polynomialToRegular_apply]
    rw [he x hx, mul_div_cancel₀ _ hx0]
  · simpa using hne P hPU

variable [IsAlgClosed k] [Finite σ]

/-- The denominators of a regular function are everything.

An ideal that is not the whole ring lies in a maximal one, which by Theorem
3.2(b) is `𝔪_P` for some point `P`; but no ideal of denominators is contained in
`𝔪_P`, since some denominator does not vanish at `P`. -/
theorem denominators_eq_top (hY : IsIrreducible Y) (hYalg : IsAlgebraicSet Y)
    {f : Y → k} (hf : IsRegular f) : denominators Y f = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨P, hP⟩ := maximalIdealAt_surjective hYalg hm
  obtain ⟨a, ha, hav⟩ := exists_mem_denominators_evalAt_ne_zero hY hf P
  exact hav (mem_maximalIdealAt.1 (hP ▸ hle ha))

/-- **Theorem 3.2(a)**, surjectivity: every regular function on an affine
variety is a polynomial function.

`1` is a denominator, and `1 · f = f` being a polynomial function is the
statement. -/
theorem coordinateToRegular_surjective (hY : IsIrreducible Y) (hYalg : IsAlgebraicSet Y)
    {f : Y → k} (hf : IsRegular f) : ∃ a : coordinateRing Y, coordinateToRegular Y a = f := by
  obtain ⟨b, hb⟩ := (denominators_eq_top hY hYalg hf).ge (Submodule.mem_top (x := (1 : _)))
  refine ⟨b, ?_⟩
  rw [← hb]
  funext x
  simp

/-- **Theorem 3.2(a)**: `A(Y) ≅ 𝒪(Y)` as `k`-algebras. -/
noncomputable def coordinateRingEquivGlobalRegular (hY : IsIrreducible Y)
    (hYalg : IsAlgebraicSet Y) : coordinateRing Y ≃ₐ[k] globalRegular Y :=
  AlgEquiv.ofBijective
    ((coordinateToRegular Y).codRestrict (globalRegular Y) coordinateToRegular_mem_globalRegular)
    ⟨fun a b hab => coordinateToRegular_injective (congrArg Subtype.val hab),
      fun f => by
        obtain ⟨a, ha⟩ := coordinateToRegular_surjective hY hYalg (mem_globalRegular.1 f.2)
        exact ⟨a, Subtype.ext ha⟩⟩

end Hartshorne
