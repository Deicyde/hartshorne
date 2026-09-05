/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.Hom

/-!
# Criterion for a morphism into an affine variety

Hartshorne, *Algebraic Geometry*, I.3, Lemma 3.6 (p. 20).

A map `φ : X → Y` from a variety to an affine variety is a morphism exactly when
each coordinate `xᵢ ∘ φ` is regular on `X`. This is the workhorse of the
section: checking `n` regular functions is finite and concrete, whereas checking
the definition of a morphism quantifies over all open subsets of `Y` and all
regular functions on them.

Necessity is the definition applied to the coordinates, which are regular on `Y`
with numerator `xᵢ` and denominator `1`. Sufficiency splits in two.

*Continuity.* Regular functions form a `k`-subalgebra, so if each `xᵢ ∘ φ` is
regular then so is `f ∘ φ` for every polynomial `f`; the preimage of `Z(T)` is
the intersection over `f ∈ T` of the zero loci of `f ∘ φ`; and zero loci of
regular functions are closed, which is Lemma 3.1.

*Pullback.* A regular function is only *locally* a quotient `g/h`, so `f ∘ φ` is
only locally `(g ∘ φ)/(h ∘ φ)`. Turning that into regularity needs locality and
closure under division by a nowhere-zero regular function.

All three facts about the source are `Variety` fields rather than consequences,
and this lemma is why: `X` is an arbitrary variety, with no definition of
regularity to appeal to.

## Main results

* `Hartshorne.Variety.continuous_of_coords_regular`
* `Hartshorne.regular_comp_of_coords_regular`
* `Hartshorne.exists_varietyHom_iff_coords_regular`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

universe u v

variable {k : Type u} [Field k] {σ : Type*}

namespace Variety

variable {X : Variety.{u, v} k} {U : Opens X.carrier}

/-- Evaluating a polynomial along a map whose coordinates are regular gives a
regular function.

Both sides are algebra maps out of `MvPolynomial σ k` agreeing on the
variables, so they agree. -/
theorem coe_aeval_coords (ψ : U → (σ → k))
    (h : ∀ i, (fun x : U => ψ x i) ∈ X.regular U) (f : MvPolynomial σ k) :
    ((aeval (fun i => (⟨fun x : U => ψ x i, h i⟩ : X.regular U)) f : X.regular U) : U → k)
      = fun x => eval (ψ x) f := by
  funext x
  have : ((Pi.evalAlgHom k (fun _ : U => k) x).comp
      ((X.regular U).val.comp (aeval fun i => (⟨fun y : U => ψ y i, h i⟩ : X.regular U))))
      = aeval (ψ x) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact congrArg (fun φ => φ f) this

/-- `x ↦ f(ψ x)` is regular whenever the coordinates of `ψ` are. -/
theorem eval_comp_mem_regular (ψ : U → (σ → k))
    (h : ∀ i, (fun x : U => ψ x i) ∈ X.regular U) (f : MvPolynomial σ k) :
    (fun x : U => eval (ψ x) f) ∈ X.regular U := by
  rw [← coe_aeval_coords ψ h f]
  exact SetLike.coe_mem _

/-- The zero locus of a globally regular function is closed on the carrier
itself, not merely on the top open subset. -/
theorem isClosed_zeroSet_of_isGlobalRegular {g : X.carrier → k}
    (hg : X.IsGlobalRegular g) : IsClosed {x : X.carrier | g x = 0} :=
  (X.isClosed_zeroLocus hg).preimage (Homeomorph.Set.univ X.carrier).symm.continuous

open scoped Hartshorne in
/-- **Half of Lemma 3.6**: a map into affine space whose coordinate functions
are regular is continuous.

This is the step that makes the criterion usable. Checking `n` regular functions
is finite and concrete; checking continuity directly quantifies over all closed
subsets of `𝔸ⁿ`. -/
theorem continuous_of_coords_regular (ψ : X.carrier → (σ → k))
    (h : ∀ i, X.IsGlobalRegular fun x => ψ x i) : Continuous ψ := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hC
  have hpre : ψ ⁻¹' zeroSet T = ⋂ f ∈ T, {x : X.carrier | eval (ψ x) f = 0} := by
    ext x
    simp [mem_zeroSet_iff]
  rw [hpre]
  refine isClosed_biInter fun f _ => isClosed_zeroSet_of_isGlobalRegular ?_
  exact eval_comp_mem_regular (fun x : (⊤ : Opens X.carrier) => ψ x.1) h f

end Variety

open scoped Hartshorne in
/-- **The other half of Lemma 3.6**: a regular function on an open subset of an
affine target pulls back to a regular function. -/
theorem regular_comp_of_coords_regular {X : Variety.{u, v} k} {Y : Set (σ → k)}
    (φ : X.carrier → Y) (hcont : Continuous φ)
    (hφ : ∀ i, X.IsGlobalRegular fun x => (φ x : σ → k) i)
    (V : Opens Y) {f : V → k} (hf : IsRegularVia (openIota V) f) :
    (fun x : Opens.comap ⟨φ, hcont⟩ V => f ⟨φ x.1, x.2⟩)
      ∈ X.regular (Opens.comap ⟨φ, hcont⟩ V) := by
  refine X.regular_of_locally fun P => ?_
  -- The local quotient for `f` at the image of `P`.
  obtain ⟨O, hO, hPO, g, h, hne, he⟩ := hf ⟨φ P.1, P.2⟩
  -- `O` is cut out of `↥Y` by an open set, whose preimage is the neighbourhood.
  rw [isOpen_induced_iff] at hO
  obtain ⟨O', hO', rfl⟩ := hO
  refine ⟨Opens.comap ⟨φ, hcont⟩ (V ⊓ ⟨O', hO'⟩), fun z hz => hz.1, ⟨P.2, hPO⟩, ?_⟩
  set W' : Opens X.carrier := Opens.comap ⟨φ, hcont⟩ (V ⊓ ⟨O', hO'⟩) with hW'
  -- On it the pullback is a quotient of two regular functions whose denominator
  -- does not vanish.
  have hcoord : ∀ i, (fun y : W' => (φ y.1 : σ → k) i) ∈ X.regular W' :=
    fun i => (hφ i).restrict W'
  have hg := Variety.eval_comp_mem_regular (fun y : W' => (φ y.1 : σ → k)) hcoord g
  have hh := Variety.eval_comp_mem_regular (fun y : W' => (φ y.1 : σ → k)) hcoord h
  have hnz : ∀ y : W', eval (φ y.1 : σ → k) h ≠ 0 := fun y => hne ⟨φ y.1, y.2.1⟩ y.2.2
  have hEq : (fun y : W' => f ⟨φ y.1, y.2.1⟩)
      = fun y : W' => eval (φ y.1 : σ → k) g / eval (φ y.1 : σ → k) h := by
    funext y
    exact he ⟨φ y.1, y.2.1⟩ y.2.2
  show (fun y : W' => f ⟨φ y.1, y.2.1⟩) ∈ X.regular W'
  rw [hEq]
  exact X.regular_div hg hh hnz

open scoped Hartshorne in
/-- **Lemma 3.6.** A map from a variety to an affine variety is a morphism
exactly when each coordinate function is regular. -/
theorem exists_varietyHom_iff_coords_regular {X : Variety k} {Y : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (φ : X.carrier → Y) :
    (∃ ρ : VarietyHom X (Variety.ofQuasiAffine hY), ρ.toFun = φ) ↔
      ∀ i, X.IsGlobalRegular fun x => (φ x : σ → k) i := by
  constructor
  · rintro ⟨ρ, rfl⟩ i
    -- The `i`-th coordinate is regular on the target: numerator `Xᵢ`.
    have hcoord : (fun y : (⊤ : Opens Y) => (y.1 : σ → k) i)
        ∈ (Variety.ofQuasiAffine hY).regular ⊤ := fun _ =>
      ⟨Set.univ, isOpen_univ, Set.mem_univ _, MvPolynomial.X i, 1, by simp, by simp⟩
    -- `ρ⁻¹(⊤) = ⊤`, definitionally, so the pullback is already global.
    exact ρ.regular_comp ⊤ _ hcoord
  · intro h
    have hψ : Continuous fun x => (φ x : σ → k) := Variety.continuous_of_coords_regular _ h
    have hcont : Continuous φ := hψ.subtype_mk fun x => (φ x).2
    exact ⟨⟨φ, hcont, fun V f hf => regular_comp_of_coords_regular φ hcont h V hf⟩, rfl⟩

end Hartshorne
