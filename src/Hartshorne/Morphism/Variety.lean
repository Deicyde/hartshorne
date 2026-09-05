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

Four conditions are imposed: restriction, closed zero loci, closure under
division by a nowhere-vanishing regular function, and locality. All four hold in
every construction here, where regularity is *defined* by the local-quotient
condition, and none of them follows from the others.

Lemma 3.6 is what fixed the list. It says a map into an affine variety is a
morphism as soon as its coordinates are regular, and it is stated for an
arbitrary source. Continuity of such a map needs closed zero loci; and the
pullback of a regular function is only *locally* a quotient of pulled-back
polynomials, so concluding that it is regular needs both division and locality.
A `Subalgebra` gives the ring operations and nothing else.

Locality was left out at first, on the argument that regularity is defined
pointwise in every construction and so is local for free. That is true and it is
beside the point: an abstract variety has no such definition to appeal to.

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
  /-- The zero locus of a regular function is closed. This is Lemma 3.1, which
  every construction below proves anyway; carrying it makes it available for an
  abstract variety, where Lemma 3.6 needs it to get continuity. -/
  isClosed_zeroLocus : ∀ {U : Opens carrier} {f : U → k}, f ∈ regular U →
    IsClosed {x : U | f x = 0}
  /-- A quotient of regular functions with nowhere-vanishing denominator is
  regular. A `Subalgebra` gives the ring operations but not this. -/
  regular_div : ∀ {U : Opens carrier} {f g : U → k}, f ∈ regular U → g ∈ regular U →
    (∀ x, g x ≠ 0) → (fun x => f x / g x) ∈ regular U
  /-- Regularity is local: a function regular near each point is regular. -/
  regular_of_locally : ∀ {U : Opens carrier} {f : U → k},
    (∀ x : U, ∃ V : Opens carrier, ∃ hVU : V ≤ U, x.1 ∈ V ∧
      (fun y : V => f ⟨y.1, hVU y.2⟩) ∈ regular V) → f ∈ regular U

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

/-- A function on the whole carrier is *globally regular* when its restriction
to the top open set is.

The detour exists because `regular` is indexed by `Opens` and so takes functions
on `↥(⊤ : Opens X)`, while a morphism takes functions on `X.carrier`. Stating
it this way keeps the two apart without any transport along the homeomorphism
between them. -/
def IsGlobalRegular (X : Variety.{u, v} k) (f : X.carrier → k) : Prop :=
  (fun x : (⊤ : Opens X.carrier) => f x.1) ∈ X.regular ⊤

/-- A globally regular function restricts to a regular function on every open
subset. -/
theorem IsGlobalRegular.restrict {X : Variety.{u, v} k} {f : X.carrier → k}
    (hf : X.IsGlobalRegular f) (U : Opens X.carrier) :
    (fun x : U => f x.1) ∈ X.regular U :=
  X.regular_restrict le_top hf

end Variety

end Hartshorne
