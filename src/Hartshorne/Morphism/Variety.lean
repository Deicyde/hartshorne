/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.RegularFunctionProj
import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Varieties

Hartshorne, *Algebraic Geometry*, I.3, the definition on p. 15.

Hartshorne's definition is "a variety over `k` is any affine, quasi-affine,
projective or quasi-projective variety". That is a list, and a list is awkward
to quantify over: Theorem 3.2, Proposition 3.5 and Lemma 3.6 all range over an
arbitrary variety `X` while constraining only `Y`, and a four-way case split
would infect every one of them.

## The representation, and why

`Variety` is a structure: a topological space together with, for each open
subset, a `k`-subalgebra of the functions on it designated *regular*, subject to
restriction and locality. Hartshorne's four cases become four constructions of
that structure rather than four constructors of an inductive type.

The alternative, an inductive sum of the four cases, was rejected. Nothing in §3
ever distinguishes the cases except Theorem 3.4, which is stated about
projective varieties specifically; and the four cases have genuinely different
carrier types, so an inductive sum would still have to bundle a type. The
bundled form is also the shape Chapter II's locally ringed spaces take.

The cost is real and is charged here: each of the four kinds must be shown to
satisfy the structure, which is what the two regular-function files supply.

Packaging regularity as a `Subalgebra` rather than a bare predicate collapses
the constant, addition, negation and multiplication axioms into one field.

## Main definitions

* `Hartshorne.Variety`
-/

universe u v

namespace Hartshorne

open TopologicalSpace

/-- A *variety* over `k`: an irreducible topological space with a designated
`k`-subalgebra of regular functions on each open subset, closed under
restriction and detected locally.

Irreducibility is part of the definition because Hartshorne's varieties are
irreducible, and because the function field is a field only for irreducible
spaces. -/
structure Variety (k : Type u) [Field k] where
  /-- The underlying topological space. -/
  carrier : Type v
  [topology : TopologicalSpace carrier]
  [irreducible : IrreducibleSpace carrier]
  /-- The regular functions on each open subset. -/
  regular : (U : Opens carrier) → Subalgebra k (U → k)
  /-- Regularity is preserved by restriction to a smaller open set. -/
  regular_restrict : ∀ {U V : Opens carrier} (h : V ≤ U) {f : U → k},
    f ∈ regular U → (fun x : V => f ⟨x.1, h x.2⟩) ∈ regular V
  /-- Regularity is local: a function regular on each piece of an open cover is
  regular. -/
  regular_of_cover : ∀ {U : Opens carrier} (f : U → k) (S : Set (Opens carrier)),
    (∀ V ∈ S, V ≤ U) → (∀ x : U, ∃ V ∈ S, (x : carrier) ∈ V) →
      (∀ V ∈ S, ∀ h : V ≤ U, (fun x : V => f ⟨x.1, h x.2⟩) ∈ regular V) →
        f ∈ regular U

attribute [instance] Variety.topology Variety.irreducible

namespace Variety

variable {k : Type u} [Field k]

instance : CoeSort (Variety.{u, v} k) (Type v) := ⟨Variety.carrier⟩

/-- The global regular functions on a variety, Hartshorne's `𝒪(Y)`. -/
abbrev globalRegular (X : Variety.{u, v} k) : Subalgebra k ((⊤ : Opens X) → k) :=
  X.regular ⊤

/-- A variety is nonempty, since an irreducible space is. -/
theorem nonempty (X : Variety.{u, v} k) : Nonempty X.carrier :=
  X.irreducible.toNonempty

end Variety

end Hartshorne
