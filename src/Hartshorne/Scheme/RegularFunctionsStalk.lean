/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyLocalRing
import Hartshorne.Scheme.RegularFunctionsSheaf
import Mathlib.Topology.Sheaves.Stalks

/-!
# The stalk of the regular-functions sheaf

Hartshorne, *Algebraic Geometry*, II.1, Example 1.0.1 (p. 62).

The categorical stalk of the Chapter II sheaf of regular functions is
canonically the quotient-of-germs local ring constructed in Chapter I.
-/

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne.Variety

universe u v

variable {k : Type u} [Field k] (X : Variety.{u, max u v} k) (P : X.carrier)

private def germRepSection (r : X.GermRep P) :
    X.regularSheaf.presheaf.obj (op r.U) :=
  ⟨r.toFun, r.regular⟩

private noncomputable def germRepToStalk (r : X.GermRep P) :
    X.regularSheaf.presheaf.stalk P :=
  X.regularSheaf.presheaf.germ r.U P r.mem_U (germRepSection X P r)

private theorem germRepToStalk_eq_of_rel {r s : X.GermRep P} (h : r.Rel s) :
    germRepToStalk X P r = germRepToStalk X P s := by
  apply X.regularSheaf.presheaf.germ_ext (r.U ⊓ s.U) ⟨r.mem_U, s.mem_U⟩
    (homOfLE inf_le_left) (homOfLE inf_le_right)
  apply Subtype.ext
  funext x
  exact h x.1 x.2.1 x.2.2

private noncomputable def localRingToStalkFun :
    X.LocalRingAt P → X.regularSheaf.presheaf.stalk P :=
  Quotient.lift (germRepToStalk X P) fun _ _ h => germRepToStalk_eq_of_rel X P h

private noncomputable def localRingToStalkRingHom :
    X.LocalRingAt P →+* X.regularSheaf.presheaf.stalk P where
  toFun := localRingToStalkFun X P
  map_one' := by
    change X.regularSheaf.presheaf.germ ⊤ P trivial 1 = 1
    simp
  map_mul' := by
    intro a b
    refine Quotient.inductionOn₂ a b fun r s => ?_
    change germRepToStalk X P (r.mul s) = germRepToStalk X P r * germRepToStalk X P s
    simp only [germRepToStalk]
    rw [← X.regularSheaf.presheaf.germ_res_apply (homOfLE inf_le_left) P
      ⟨r.mem_U, s.mem_U⟩ (germRepSection X P r),
      ← X.regularSheaf.presheaf.germ_res_apply (homOfLE inf_le_right) P
        ⟨r.mem_U, s.mem_U⟩ (germRepSection X P s), ← map_mul]
    rfl
  map_zero' := by
    change X.regularSheaf.presheaf.germ ⊤ P trivial 0 = 0
    simp
  map_add' := by
    intro a b
    refine Quotient.inductionOn₂ a b fun r s => ?_
    change germRepToStalk X P (r.add s) = germRepToStalk X P r + germRepToStalk X P s
    simp only [germRepToStalk]
    rw [← X.regularSheaf.presheaf.germ_res_apply (homOfLE inf_le_left) P
      ⟨r.mem_U, s.mem_U⟩ (germRepSection X P r),
      ← X.regularSheaf.presheaf.germ_res_apply (homOfLE inf_le_right) P
        ⟨r.mem_U, s.mem_U⟩ (germRepSection X P s), ← map_add]
    rfl

private theorem localRingToStalkRingHom_surjective :
    Function.Surjective (localRingToStalkRingHom X P) := by
  intro z
  obtain ⟨U, hPU, s, hs⟩ := X.regularSheaf.presheaf.exists_germ_eq z
  let r : X.GermRep P :=
    { U := U
      mem_U := hPU
      toFun := s.1
      regular := s.2 }
  refine ⟨Quotient.mk (X.germSetoid P) r, ?_⟩
  exact hs

private theorem localRingToStalkRingHom_injective :
    Function.Injective (localRingToStalkRingHom X P) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun r s h => ?_
  apply Quotient.sound
  obtain ⟨W, hPW, iWr, iWs, hrs⟩ := X.regularSheaf.presheaf.germ_eq
    P r.mem_U s.mem_U (germRepSection X P r) (germRepSection X P s) h
  let t : X.GermRep P :=
    { U := W
      mem_U := hPW
      toFun := fun x => r.toFun ⟨x.1, iWr.le x.2⟩
      regular := X.regular_restrict iWr.le r.regular }
  apply GermRep.rel_trans (s := t)
  · intro x hx hxt
    rfl
  · intro x hxt hxs
    have hsections :
        X.regularRestriction iWr.le (germRepSection X P r) =
          X.regularRestriction iWs.le (germRepSection X P s) := hrs
    exact congrArg (fun q => q.1 ⟨x, hxt⟩) hsections

/-- **Hartshorne II.1, Example 1.0.1.** The categorical stalk of the sheaf of
regular functions at `P` is canonically the quotient-of-germs local ring
constructed in Chapter I. -/
noncomputable def regularSheafStalkEquivLocalRing :
    X.regularSheaf.presheaf.stalk P ≃+* X.LocalRingAt P :=
  (RingEquiv.ofBijective (localRingToStalkRingHom X P)
    ⟨localRingToStalkRingHom_injective X P, localRingToStalkRingHom_surjective X P⟩).symm

/-- The stalk equivalence sends the categorical germ of a regular section to
its existing quotient-of-germs representative. -/
@[simp]
theorem regularSheafStalkEquivLocalRing_germ (U : Opens X.carrier) (hPU : P ∈ U)
    (s : X.regularSheaf.presheaf.obj (op U)) :
    regularSheafStalkEquivLocalRing X P (X.regularSheaf.presheaf.germ U P hPU s) =
      Quotient.mk (X.germSetoid P)
        ({ U := U, mem_U := hPU, toFun := s.1, regular := s.2 } : X.GermRep P) := by
  let e : X.LocalRingAt P ≃+* X.regularSheaf.presheaf.stalk P :=
    RingEquiv.ofBijective (localRingToStalkRingHom X P)
      ⟨localRingToStalkRingHom_injective X P, localRingToStalkRingHom_surjective X P⟩
  change e.symm (X.regularSheaf.presheaf.germ U P hPU s) = _
  apply e.injective
  rw [e.apply_symm_apply]
  rfl

end Hartshorne.Variety
