/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.Hom

/-!
# Maps into affine space with regular coordinates

Hartshorne, *Algebraic Geometry*, I.3, the first half of Lemma 3.6 (p. 20).

Lemma 3.6 says a map `ψ : X → Y` into an affine variety is a morphism exactly
when each coordinate `xᵢ ∘ ψ` is regular. This file proves the part of the
sufficiency direction that is about the topology: if the coordinates of a map
into `𝔸ⁿ` are regular, the map is continuous.

The argument is Hartshorne's. Regular functions form a `k`-subalgebra, so if
each `xᵢ ∘ ψ` is regular then so is `f ∘ ψ` for every polynomial `f`; the
preimage of the closed set `Z(T)` is the intersection over `f ∈ T` of the zero
loci of `f ∘ ψ`; and zero loci of regular functions are closed, which is
Lemma 3.1.

"Regular functions form a subalgebra" is doing the work, and the proof below
spends most of its length making that precise: `aeval` into the subalgebra
`X.regular U` gives regularity for free, and one application of
`MvPolynomial.algHom_ext` identifies the result with `x ↦ f(ψ x)`.

## Main results

* `Hartshorne.Variety.continuous_of_coords_regular`
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

/-- The zero locus of `f ∘ ψ` is closed, for any polynomial `f`. -/
theorem isClosed_zeroLocus_comp (ψ : U → (σ → k))
    (h : ∀ i, (fun x : U => ψ x i) ∈ X.regular U) (f : MvPolynomial σ k) :
    IsClosed {x : U | eval (ψ x) f = 0} := by
  have hmem : (fun x : U => eval (ψ x) f) ∈ X.regular U := by
    rw [← coe_aeval_coords ψ h f]
    exact SetLike.coe_mem _
  exact X.isClosed_zeroLocus hmem

open scoped Hartshorne in
/-- **Half of Lemma 3.6**: a map into affine space whose coordinate functions
are regular is continuous.

This is the step that makes the criterion usable. Checking `n` regular functions
is finite and concrete; checking continuity directly quantifies over all closed
subsets of `𝔸ⁿ`. -/
theorem continuous_of_coords_regular (ψ : U → (σ → k))
    (h : ∀ i, (fun x : U => ψ x i) ∈ X.regular U) : Continuous ψ := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hC
  have : ψ ⁻¹' zeroSet T = ⋂ f ∈ T, {x : U | eval (ψ x) f = 0} := by
    ext x
    simp [mem_zeroSet_iff]
  rw [this]
  exact isClosed_biInter fun f _ => isClosed_zeroLocus_comp ψ h f

end Variety

end Hartshorne
