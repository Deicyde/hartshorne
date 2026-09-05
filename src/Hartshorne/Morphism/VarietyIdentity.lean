/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.Variety

/-!
# The identity principle for an arbitrary variety

Hartshorne, *Algebraic Geometry*, I.3, Remark 3.1.1, for a bundled `Variety`.

Two regular functions on an open subset of a variety that agree on a nonempty
open subset agree everywhere on it.

The affine and projective versions of this were each proved from Lemma 3.1 in
their own coordinates. Here it is proved once, for any `Variety`, from the
structure alone: regular functions form a subalgebra, so their difference is
regular, and the zero locus of a regular function is closed. Nothing about
polynomials is used.

That the structure now suffices is a consequence of the fields Lemma 3.6 forced.
The payoff is that germs and the function field can be built for an arbitrary
variety rather than separately in each set of coordinates, which is what
Theorem 3.4 needs: it is about `𝒪_P` and `K(Y)` for a *projective* `Y`, and
those do not exist yet.

## Main results

* `Hartshorne.Variety.preirreducible_univ`
* `Hartshorne.Variety.eq_of_eqOn`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X : Variety.{u, v} k}

namespace Variety

/-- An open subset of a variety is irreducible as a space. -/
theorem preirreducible_univ (U : Opens X.carrier) :
    IsPreirreducible (Set.univ : Set U) := by
  have hXu : IsPreirreducible (Set.univ : Set X.carrier) :=
    PreirreducibleSpace.isPreirreducible_univ
  have hUpre : IsPreirreducible (U : Set X.carrier) := by
    simpa using IsPreirreducible.inter_isOpen hXu U.isOpen
  have : PreirreducibleSpace U := isPreirreducible_iff_preirreducibleSpace.1 hUpre
  exact PreirreducibleSpace.isPreirreducible_univ

/-- **The identity principle.** Two regular functions on `U` agreeing on a
nonempty open subset of `U` are equal.

Their difference is regular, its zero locus is closed, and a nonempty open
subset of an irreducible space is dense. -/
theorem eq_of_eqOn {U : Opens X.carrier} {f g : U → k}
    (hf : f ∈ X.regular U) (hg : g ∈ X.regular U)
    {V : Set U} (hV : IsOpen V) (hVne : V.Nonempty) (heq : Set.EqOn f g V) : f = g := by
  have hUirr : IsPreirreducible (Set.univ : Set U) := preirreducible_univ U
  -- The locus where `f` and `g` agree is closed, being the zero locus of `f - g`.
  have hcl : IsClosed {x : U | (f - g) x = 0} :=
    X.isClosed_zeroLocus (Subalgebra.sub_mem _ hf hg)
  have hcl' : IsClosed {x : U | f x = g x} := by
    convert hcl using 2 with x
    simp [sub_eq_zero]
  -- `V` is dense, so the agreement locus is everything.
  have hdense : Dense V := by
    rw [dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    intro x _
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨z, -, hz⟩ := hUirr o V ho hV ⟨x, Set.mem_univ x, hxo⟩
      (hVne.mono fun _ h => ⟨Set.mem_univ _, h⟩)
    exact ⟨z, hz.1, hz.2⟩
  have hsub : closure V ⊆ {x : U | f x = g x} := by
    rw [← hcl'.closure_eq]
    exact closure_mono fun x hx => heq hx
  funext x
  exact hsub (by rw [hdense.closure_eq]; trivial)

end Variety

end Hartshorne
