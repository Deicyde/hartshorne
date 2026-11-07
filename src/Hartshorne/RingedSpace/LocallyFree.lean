/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ModuleSheafTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Locally free and invertible module sheaves on a ringed space

Hartshorne, *Algebraic Geometry*, II.5 (p. 109).

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`; `𝒪_X`-modules are `SheafOfModules (ringCatSheafOf R)`. The restriction `F|_U` of an
`𝒪_X`-module to an open `U` is the module sheaf `F.over U` over `𝒪_X|_U` on the opens contained
in `U`.

A module sheaf is *free* (`Hartshorne.Ringed.IsFree`) if it is isomorphic to a direct sum of
copies of the structure sheaf (Mathlib's `SheafOfModules.free I`). An `𝒪_X`-module `F` is
*locally free* (`IsLocallyFree`) if `X` is covered by opens `U` with `F|_U` free, *locally free
of rank `r`* (`IsLocallyFreeOfRank`) if moreover each `F|_U` can be taken to be a direct sum of
`r` copies of `𝒪_U`, and *invertible* (`IsInvertible`) if it is locally free of rank one. It is
*locally free of finite rank* (`IsFiniteLocallyFree`) if each point has an open neighbourhood
`U` on which `F|_U` is a direct sum of finitely many copies of `𝒪_U`; this is the hypothesis of
the finite-rank duality statements, and needs no notion of rank.

For a scheme `X`, `X.Modules` is definitionally `SheafOfModules (ringCatSheafOf X.sheaf)`;
`Hartshorne.Scheme.LocallyFreeRinged` compares these predicates with the scheme ones, phrased
through restriction to open subschemes.
-/

universe u v₁ u₁

open CategoryTheory Limits TopologicalSpace

namespace Hartshorne

namespace Ringed

section Free

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules is *free* if it is isomorphic to a direct sum of copies of the structure
sheaf. -/
def IsFree (M : SheafOfModules.{u} S) : Prop :=
  ∃ I : Type u, Nonempty (M ≅ SheafOfModules.free I)

end Free

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- An `𝒪_X`-module `F` is *locally free* if `X` is covered by open sets `U` for which the
restriction `F|_U` is a free `𝒪_U`-module. -/
def IsLocallyFree (F : SheafOfModules.{u} (ringCatSheafOf R)) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsFree (F.over U)

/-- An `𝒪_X`-module `F` is *locally free of rank `r`* if `X` is covered by open sets `U` for
which `F|_U` is isomorphic to a direct sum of `r` copies of `𝒪_U`. -/
def IsLocallyFreeOfRank (F : SheafOfModules.{u} (ringCatSheafOf R)) (r : ℕ) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ Nonempty (F.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))

/-- An `𝒪_X`-module `F` is *invertible* if it is locally free of rank one. -/
def IsInvertible (F : SheafOfModules.{u} (ringCatSheafOf R)) : Prop :=
  IsLocallyFreeOfRank F 1

/-- An `𝒪_X`-module `F` is *locally free of finite rank* if every point has an open
neighbourhood `U` on which `F|_U` is isomorphic to a direct sum of finitely many copies of
`𝒪_U`. -/
def IsFiniteLocallyFree (F : SheafOfModules.{u} (ringCatSheafOf R)) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    ∃ r : ℕ, Nonempty (F.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))

/-- A module locally free of rank `r` is locally free of finite rank. -/
theorem IsLocallyFreeOfRank.isFiniteLocallyFree {F : SheafOfModules.{u} (ringCatSheafOf R)}
    {r : ℕ} (hF : IsLocallyFreeOfRank F r) : IsFiniteLocallyFree F := fun x => by
  obtain ⟨U, hxU, hU⟩ := hF x
  exact ⟨U, hxU, r, hU⟩

/-- An invertible module is locally free of finite rank. -/
theorem IsInvertible.isFiniteLocallyFree {F : SheafOfModules.{u} (ringCatSheafOf R)}
    (hF : IsInvertible F) : IsFiniteLocallyFree F :=
  IsLocallyFreeOfRank.isFiniteLocallyFree hF

/-- A module locally free of finite rank is locally free. -/
theorem IsFiniteLocallyFree.isLocallyFree {F : SheafOfModules.{u} (ringCatSheafOf R)}
    (hF : IsFiniteLocallyFree F) : IsLocallyFree F := fun x => by
  obtain ⟨U, hxU, r, hU⟩ := hF x
  exact ⟨U, hxU, ULift.{u} (Fin r), hU⟩

/-- A module locally free of rank `r` is locally free. -/
theorem IsLocallyFreeOfRank.isLocallyFree {F : SheafOfModules.{u} (ringCatSheafOf R)}
    {r : ℕ} (hF : IsLocallyFreeOfRank F r) : IsLocallyFree F :=
  hF.isFiniteLocallyFree.isLocallyFree

end Ringed

end Hartshorne
