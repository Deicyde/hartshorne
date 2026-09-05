/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.OpenSubvariety
import Hartshorne.Morphism.VarietyFunctionFieldHom

/-!
# The function field does not see beyond a nonempty open subset

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(c).

For `Z ⊆ Y` quasi-projective with `Z` open in `Y`, the inclusion induces an
isomorphism `K(Y) ≅ K(Z)`.

This is the function-field counterpart of the corresponding statement for local
rings, and it is where the function field is easier: a rational function has no
base point, so the inclusion needs no more than dense range, which a nonempty
open subset of an irreducible space has automatically.

Injectivity is the identity principle, exactly as for germs. Surjectivity pushes
a representative forward, reusing the machinery built for germs unchanged; only
the nonemptiness obligation is new, and it is immediate, since a nonempty open
subset of `Z` is a nonempty open subset of `Y`.

## Main results

* `Hartshorne.bijective_functionFieldHom_inclHom`
-/

namespace Hartshorne

open TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y Z : Set (ProjectiveSpace k σ)}
  (hY : IsQuasiProjVariety Y) (hZ : IsQuasiProjVariety Z) (hZY : Z ⊆ Y)
  (hopen : IsOpen {y : Y | y.1 ∈ Z})

include hZ hopen in
/-- The inclusion of an open piece has dense range: its range is the nonempty
open set `Z`, and a nonempty open subset of an irreducible space is dense. -/
theorem dense_range_inclHom :
    Dense (Set.range (inclHom hY hZ hZY).toFun) := by
  have hrange : Set.range (inclHom hY hZ hZY).toFun = {y : Y | y.1 ∈ Z} := by
    ext y
    exact ⟨by rintro ⟨x, rfl⟩; exact x.2, fun h => ⟨⟨y.1, h⟩, rfl⟩⟩
  rw [hrange]
  obtain ⟨z, hz⟩ := hZ.1
  exact Variety.dense_of_isOpen_of_nonempty hopen ⟨⟨z, hZY hz⟩, hz⟩

/-- Pushing a rational function on `Z` forward to one on `Y`. -/
noncomputable def pushRat (t : Variety.RationalRep (Variety.ofQuasiProjective hZ)) :
    Variety.RationalRep (Variety.ofQuasiProjective hY) where
  U := ⟨_, isOpen_pushOpens hZ hopen t.U⟩
  nonempty_U := by
    obtain ⟨z, hz⟩ := t.nonempty_U
    exact ⟨⟨z.1, hZY z.2⟩, z.2, hz⟩
  toFun := fun y => t.toFun (pullPoint hY hZ (U := t.U)
    (V := ⟨_, isOpen_pushOpens hZ hopen t.U⟩) (fun _ => Iff.rfl) y)
  regular := regular_pullPoint hY hZ (fun _ => Iff.rfl) t.toFun t.regular

include hopen in
/-- **`K(Y) = K(Z)` for `Z` a nonempty open subset.**

Injectivity is the identity principle: two rational functions on `Y` whose
restrictions to `Z` agree agree on the overlap of their domains, because `Z`
meets that overlap in a nonempty open set. Surjectivity is `pushRat`. -/
theorem bijective_functionFieldHom_inclHom :
    Function.Bijective ((inclHom hY hZ hZY).functionFieldHom
      (dense_range_inclHom hY hZ hZY hopen)) := by
  constructor
  · refine Quotient.ind fun r => Quotient.ind fun s => fun hrs => ?_
    have hrel := Quotient.exact hrs
    refine Quotient.sound ?_
    set U : Opens (Variety.ofQuasiProjective hY).carrier := r.U ⊓ s.U with hU
    have hfr : (fun x : U => r.toFun ⟨x.1, x.2.1⟩) ∈ (Variety.ofQuasiProjective hY).regular U :=
      (Variety.ofQuasiProjective hY).regular_restrict inf_le_left r.regular
    have hfs : (fun x : U => s.toFun ⟨x.1, x.2.2⟩) ∈ (Variety.ofQuasiProjective hY).regular U :=
      (Variety.ofQuasiProjective hY).regular_restrict inf_le_right s.regular
    have hVopen : IsOpen {x : U | x.1.1 ∈ Z} := hopen.preimage continuous_subtype_val
    -- Nonemptiness of the triple overlap is irreducibility, not a shared point.
    have hVne : ({x : U | x.1.1 ∈ Z}).Nonempty := by
      obtain ⟨z, hzU, hzZ⟩ := Variety.opens_inter_nonempty (U := U)
        (V := (⟨_, hopen⟩ : Opens (Variety.ofQuasiProjective hY).carrier))
        (Variety.opens_inter_nonempty r.nonempty_U s.nonempty_U) (by
          obtain ⟨z, hz⟩ := hZ.1
          exact ⟨⟨z, hZY hz⟩, hz⟩)
      exact ⟨⟨z, hzU⟩, hzZ⟩
    have heq := Variety.eq_of_eqOn hfr hfs hVopen hVne fun x hx =>
      hrel ⟨x.1.1, hx⟩ x.2.1 x.2.2
    exact fun y hr hs => congrFun heq ⟨y, hr, hs⟩
  · refine Quotient.ind fun t => ?_
    refine ⟨Quotient.mk (Variety.rationalSetoid (Variety.ofQuasiProjective hY))
      (pushRat hY hZ hZY hopen t), Quotient.sound ?_⟩
    intro x _ _
    rfl

end Hartshorne
