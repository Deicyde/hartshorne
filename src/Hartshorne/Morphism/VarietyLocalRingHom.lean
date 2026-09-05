/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyLocalRing
import Hartshorne.Morphism.Hom

/-!
# Local rings are functorial

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(b).

A morphism `φ : X → Y` pulls germs at `φ(P)` back to germs at `P`, giving a ring
map `𝒪_{φ(P),Y} → 𝒪_{P,X}`, contravariantly functorial.

This is what transports local rings along the chart isomorphism, which is how
Theorem 3.4(b) reaches the affine results from a projective `Y`. The
construction is immediate: the pullback of a germ is the pullback of a
representative, and that a morphism pulls regular functions back to regular
functions is the definition of a morphism.

## Main definitions

* `Hartshorne.VarietyHom.germPullback`, `Hartshorne.VarietyHom.localRingHom`

## Main results

* `Hartshorne.VarietyHom.localRingHom_id`, `Hartshorne.VarietyHom.localRingHom_comp`
* `Hartshorne.VarietyHom.bijective_localRingHom_of_isIso`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X Y Z : Variety.{u, v} k}

namespace VarietyHom

/-- Pulling a germ representative back along a morphism. -/
noncomputable def germPullback (f : VarietyHom X Y) (P : X.carrier)
    (r : Variety.GermRep Y (f P)) : Variety.GermRep X P where
  U := Opens.comap ⟨f.toFun, f.continuous_toFun⟩ r.U
  mem_U := r.mem_U
  toFun := fun x => r.toFun ⟨f x.1, x.2⟩
  regular := f.regular_comp r.U r.toFun r.regular

theorem germPullback_congr (f : VarietyHom X Y) (P : X.carrier)
    {r s : Variety.GermRep Y (f P)} (h : r.Rel s) :
    (f.germPullback P r).Rel (f.germPullback P s) :=
  fun x hr hs => h (f x) hr hs

/-- The induced map `𝒪_{φ(P),Y} → 𝒪_{P,X}`. -/
noncomputable def localRingHom (f : VarietyHom X Y) (P : X.carrier) :
    Variety.LocalRingAt Y (f P) →+* Variety.LocalRingAt X P where
  toFun := Quotient.map (f.germPullback P) fun _ _ h => f.germPullback_congr P h
  map_one' := Quotient.sound fun _ _ _ => rfl
  map_zero' := Quotient.sound fun _ _ _ => rfl
  map_mul' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl
  map_add' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl

@[simp]
theorem localRingHom_mk (f : VarietyHom X Y) (P : X.carrier)
    (r : Variety.GermRep Y (f P)) :
    f.localRingHom P (Quotient.mk (Variety.germSetoid Y (f P)) r)
      = Quotient.mk (Variety.germSetoid X P) (f.germPullback P r) :=
  rfl

theorem localRingHom_id (X : Variety.{u, v} k) (P : X.carrier) :
    (VarietyHom.id X).localRingHom P = RingHom.id (Variety.LocalRingAt X P) := by
  refine RingHom.ext ?_
  refine Quotient.ind fun r => ?_
  exact Quotient.sound fun _ _ _ => rfl

/-- Pullback of local rings is contravariantly functorial. -/
theorem localRingHom_comp (g : VarietyHom Y Z) (f : VarietyHom X Y) (P : X.carrier) :
    (g.comp f).localRingHom P
      = (f.localRingHom P).comp (g.localRingHom (f P)) := by
  refine RingHom.ext ?_
  refine Quotient.ind fun r => ?_
  exact Quotient.sound fun _ _ _ => rfl

/-- **An isomorphism of varieties induces an isomorphism of local rings.**

Both halves are proved on representatives rather than by composing the two ring
maps. Composing them would need a transport along `g(f(P)) = P`, since the
inverse morphism's map on local rings is indexed by `g(f(P))` and not by `P`;
working with germs avoids the dependent rewrite entirely.

Injectivity needs only that `f` is surjective on points: two germs whose
pullbacks agree agree, because every point of `Y` is `f` of something.
Surjectivity pushes a germ forward along the inverse morphism. -/
theorem bijective_localRingHom_of_isIso {f : VarietyHom X Y} (hf : f.IsIso)
    (P : X.carrier) : Function.Bijective (f.localRingHom P) := by
  obtain ⟨g, hgf, hfg⟩ := hf
  have hgfx : ∀ x : X.carrier, g (f x) = x := congrFun (congrArg VarietyHom.toFun hgf)
  have hfgy : ∀ y : Y.carrier, f (g y) = y := congrFun (congrArg VarietyHom.toFun hfg)
  constructor
  · refine Quotient.ind fun r => Quotient.ind fun s => fun hrs => ?_
    have hrel := Quotient.exact hrs
    refine Quotient.sound fun y hr hs => ?_
    have hy : f (g y) = y := hfgy y
    have h := hrel (g y) (show f (g y) ∈ r.U by rw [hy]; exact hr)
      (show f (g y) ∈ s.U by rw [hy]; exact hs)
    simpa [germPullback, hy] using h
  · refine Quotient.ind fun t => ?_
    refine ⟨Quotient.mk _ (g.germPullback (f P)
      ⟨t.U, by rw [hgfx]; exact t.mem_U, t.toFun, t.regular⟩), ?_⟩
    refine Quotient.sound fun x hr hs => ?_
    have hx : g (f x) = x := hgfx x
    show t.toFun ⟨g (f x), _⟩ = t.toFun ⟨x, hs⟩
    simp [hx]

end VarietyHom

end Hartshorne
