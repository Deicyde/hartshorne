/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.SurfaceCurveConvention
import Mathlib.AlgebraicGeometry.Birational.Birational
import Hartshorne.Scheme.FiniteType

/-!
# Algebraically contractible curves

Hartshorne, *Algebraic Geometry*, V, Remark 5.7.2 (p. 417).

An irreducible curve `Y` on a surface `X` is *algebraically contractible* if there are a variety
`X₀` over `k` (integral, separated and of finite type; not necessarily projective, possibly
singular), a point `P ∈ X₀` and a birational morphism `f : X ⟶ X₀` over `k` with `f(Y) = {P}` such
that `f` restricts to an isomorphism `X - Y ≅ X₀ - P`.

* `Hartshorne.Surface.AlgebraicContraction S Y`: the data of such a contraction.
* `Hartshorne.Surface.IsAlgebraicallyContractible S Y`: such a contraction exists.
* `Hartshorne.Surface.AlgebraicContraction.partialIso`, `birationalOver`: the contraction is
  birational over `k`: it gives an isomorphism between the dense open subschemes `X - Y` and
  `X₀ - P`, compatible with the structure maps.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Order TopologicalSpace

namespace Hartshorne

namespace Surface

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Surface k)

/-- The open complement `X - Y` of an irreducible curve `Y` on a surface. -/
def curveComplement (Y : S.X.PrimeDivisor) : S.X.Opens :=
  ⟨(closure {Y.1})ᶜ, isClosed_closure.isOpen_compl⟩

/-- An **algebraic contraction** of the irreducible curve `Y` on the surface `X`: a variety `X₀`
over `k` (an integral scheme, separated and of finite type over `k`; not necessarily projective,
possibly singular), a closed point `P ∈ X₀` and a morphism `f : X ⟶ X₀` over `k` with
`f(Y) = {P}`, such that `f⁻¹(X₀ - P) = X - Y` and `f : X - Y ⟶ X₀ - P` is an isomorphism. -/
structure AlgebraicContraction (Y : S.X.PrimeDivisor) where
  /-- The target surface. -/
  X₀ : Scheme.{u}
  /-- Its structure morphism to `Spec k`. -/
  hom₀ : X₀ ⟶ Spec (.of k)
  [isIntegral₀ : IsIntegral X₀]
  /-- The target is separated over `k`. -/
  [isSeparated₀ : IsSeparated hom₀]
  /-- The target is of finite type over `k`. -/
  finiteType₀ : FiniteType hom₀
  /-- The point to which `Y` is contracted. -/
  P : X₀
  isClosed_P : IsClosed ({P} : Set X₀)
  /-- The contraction morphism. -/
  f : S.X ⟶ X₀
  /-- The contraction is a morphism over `k`. -/
  comp_hom₀ : f ≫ hom₀ = S.hom
  /-- `f(Y) = {P}`. -/
  image_eq : f '' closure {Y.1} = {P}
  /-- `f⁻¹(X₀ - P) = X - Y`. -/
  preimage_compl : f ⁻¹ᵁ ⟨{P}ᶜ, isClosed_P.isOpen_compl⟩ = S.curveComplement Y
  /-- `f : X - Y ⟶ X₀ - P` is an isomorphism. -/
  isIso_restrict : IsIso (f ∣_ ⟨{P}ᶜ, isClosed_P.isOpen_compl⟩)

/-- **Algebraically contractible curves** (Hartshorne V, Remark 5.7.2). An irreducible curve `Y`
on a surface `X` is algebraically contractible if it admits an algebraic contraction: a
birational morphism `f : X ⟶ X₀` over `k` to a variety, with `f(Y)` a point `P` and
`f : X - Y ⟶ X₀ - P` an isomorphism. The target need not be projective and may be singular. -/
def IsAlgebraicallyContractible (Y : S.X.PrimeDivisor) : Prop :=
  Nonempty (S.AlgebraicContraction Y)

namespace AlgebraicContraction

attribute [instance] isIntegral₀ isSeparated₀

variable {S} {Y : S.X.PrimeDivisor} (c : S.AlgebraicContraction Y)

instance : LocallyOfFiniteType c.hom₀ := c.finiteType₀.1

instance : QuasiCompact c.hom₀ := c.finiteType₀.2

theorem dense_curveComplement : Dense (S.curveComplement Y : Set S.X) := by
  refine (S.curveComplement Y).isOpen.dense ?_
  refine ⟨genericPoint S.X, fun h ↦ ?_⟩
  have hgen : Y.1 ⤳ genericPoint S.X := specializes_iff_mem_closure.2 h
  have hle : genericPoint S.X ⤳ Y.1 := (genericPoint_spec S.X).specializes trivial
  have heq : Y.1 = genericPoint S.X := (hgen.antisymm hle).eq
  have hmax : IsMax (genericPoint S.X) := fun z _ ↦ (genericPoint_spec S.X).specializes trivial
  have h0 := coheight_eq_zero.mpr hmax
  rw [← heq, Y.2] at h0
  exact one_ne_zero h0

theorem dense_compl_P : Dense ({c.P}ᶜ : Set c.X₀) := by
  refine c.isClosed_P.isOpen_compl.dense ?_
  obtain ⟨x, hx⟩ := (dense_curveComplement (S := S) (Y := Y)).nonempty
  rw [← c.preimage_compl] at hx
  exact ⟨c.f x, hx⟩

/-- **The contraction is birational**: it restricts to an isomorphism between the dense open
subschemes `X - Y` of `X` and `X₀ - P` of `X₀`. -/
def partialIso : S.X.PartialIso c.X₀ where
  source := c.f ⁻¹ᵁ ⟨{c.P}ᶜ, c.isClosed_P.isOpen_compl⟩
  dense_source := by
    rw [c.preimage_compl]
    exact dense_curveComplement
  target := ⟨{c.P}ᶜ, c.isClosed_P.isOpen_compl⟩
  dense_target := c.dense_compl_P
  iso :=
    haveI := c.isIso_restrict
    asIso (c.f ∣_ ⟨{c.P}ᶜ, c.isClosed_P.isOpen_compl⟩)

/-- The contraction is birational over `k`. -/
theorem birationalOver : Scheme.BirationalOver S.hom c.hom₀ := by
  refine ⟨c.partialIso, ?_⟩
  change c.f ∣_ _ ≫ Scheme.Opens.ι _ ≫ c.hom₀ = Scheme.Opens.ι _ ≫ S.hom
  rw [morphismRestrict_ι_assoc, c.comp_hom₀]

end AlgebraicContraction

end

end Surface

end Hartshorne
