/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.OpenSubvariety
import Hartshorne.Rational.MorphismAgreement

/-!
# Rational maps

Hartshorne, *Algebraic Geometry*, I.4, the definition on p. 24.

A *rational map* `φ : X ⇢ Y` is an equivalence class of pairs `⟨U, φ_U⟩` with `U`
a nonempty open subset of `X` and `φ_U : U → Y` a morphism, two pairs being
equivalent when the morphisms agree on the overlap of their domains. It is
*dominant* when the image of a representative is dense.

A rational map is not a map of sets from `X` to `Y`, and nothing here pretends
it is.

## Why this needs Lemma 4.1

Reflexivity and symmetry are immediate. Transitivity is not: from agreement on
`U ∩ V` and on `V ∩ W` all that follows directly is agreement on `U ∩ V ∩ W`,
which is a nonempty open subset of `U ∩ W` rather than all of it. Lemma 4.1,
applied on the variety `U ∩ W`, closes the gap. Irreducibility of `X` is what
makes the triple overlap nonempty.

The same shape appeared in §3 for rational *functions*, where the identity
principle for regular functions sufficed because the target was `k`. For an
arbitrary target it does not, and separatedness of the target is the
replacement. The target is therefore required to be separated, which by Lemma
4.1 every quasi-projective variety is — so every variety in Hartshorne's sense.

## Main definitions

* `Hartshorne.RatMapRep`, `Hartshorne.RatMapRep.Rel`
* `Hartshorne.ratMapSetoid`, `Hartshorne.RatMap`
* `Hartshorne.RatMapRep.IsDominant`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X Y : Variety.{u, v} k}

/-- A representative of a rational map: a morphism defined on a nonempty open
subset of `X`. -/
structure RatMapRep (X Y : Variety.{u, v} k) where
  /-- The domain of definition. -/
  U : Opens X.carrier
  /-- It is nonempty. -/
  nonempty_U : (U : Set X.carrier).Nonempty
  /-- The morphism defined there. -/
  hom : VarietyHom (X.restrict U nonempty_U) Y

/-- The value of a representative at a point of its domain. -/
def RatMapRep.eval (r : RatMapRep X Y) {x : X.carrier} (hx : x ∈ r.U) : Y.carrier :=
  r.hom ⟨x, hx⟩

/-- Hartshorne's identification: two representatives are equivalent when they
agree wherever both are defined. -/
def RatMapRep.Rel (r s : RatMapRep X Y) : Prop :=
  ∀ (x : X.carrier) (hr : x ∈ r.U) (hs : x ∈ s.U), r.eval hr = s.eval hs

theorem RatMapRep.rel_refl (r : RatMapRep X Y) : r.Rel r := fun _ _ _ => rfl

theorem RatMapRep.rel_symm {r s : RatMapRep X Y} (h : r.Rel s) : s.Rel r :=
  fun x hs hr => (h x hr hs).symm

/-- **Transitivity of the identification on rational maps.**

Restrict both outer representatives to `U ∩ W`, a variety since it is a nonempty
open subset of one. They agree on the trace of `V`, which is open and nonempty,
so separatedness of the target makes them equal on all of `U ∩ W`. -/
theorem RatMapRep.rel_trans (hY : Y.IsSeparated) {r s t : RatMapRep X Y}
    (hrs : r.Rel s) (hst : s.Rel t) : r.Rel t := by
  intro x hr ht
  set W : Opens X.carrier := r.U ⊓ t.U with hW
  have hWne : (W : Set X.carrier).Nonempty :=
    Variety.opens_inter_nonempty r.nonempty_U t.nonempty_U
  -- The two outer morphisms, restricted to `U ∩ W`.
  set α : VarietyHom (X.restrict W hWne) Y :=
    r.hom.comp (Variety.inclHomOfLE X inf_le_left hWne r.nonempty_U) with hα
  set β : VarietyHom (X.restrict W hWne) Y :=
    t.hom.comp (Variety.inclHomOfLE X inf_le_right hWne t.nonempty_U) with hβ
  -- They agree on the trace of the middle domain, which is open and nonempty.
  have hopen : IsOpen {y : (X.restrict W hWne).carrier | y.1 ∈ s.U} :=
    s.U.isOpen.preimage continuous_subtype_val
  have hne : ({y : (X.restrict W hWne).carrier | y.1 ∈ s.U}).Nonempty := by
    obtain ⟨z, hzW, hzs⟩ := Variety.opens_inter_nonempty (U := W) (V := s.U) hWne s.nonempty_U
    exact ⟨⟨z, hzW⟩, hzs⟩
  have heq : ∀ y ∈ {y : (X.restrict W hWne).carrier | y.1 ∈ s.U}, α y = β y := by
    intro y hy
    exact (hrs y.1 y.2.1 hy).trans (hst y.1 hy y.2.2)
  have hαβ := hY _ α β _ hopen hne heq
  exact congrArg (fun f : VarietyHom (X.restrict W hWne) Y => f.toFun ⟨x, ⟨hr, ht⟩⟩) hαβ

/-- Rational maps, as a setoid. The target has to be separated for this to be
one. -/
def ratMapSetoid (X Y : Variety.{u, v} k) (hY : Y.IsSeparated) :
    Setoid (RatMapRep X Y) where
  r := RatMapRep.Rel
  iseqv := ⟨RatMapRep.rel_refl, RatMapRep.rel_symm, RatMapRep.rel_trans hY⟩

/-- **Hartshorne's rational maps `X ⇢ Y`.** -/
def RatMap (X Y : Variety.{u, v} k) (hY : Y.IsSeparated) : Type _ :=
  Quotient (ratMapSetoid X Y hY)

/-- A representative is *dominant* when its image is dense in the target. -/
def RatMapRep.IsDominant (r : RatMapRep X Y) : Prop :=
  Dense (Set.range fun x : (X.restrict r.U r.nonempty_U).carrier => r.hom x)

/-- **Dominance does not depend on the representative.**

Two equivalent representatives agree on the overlap of their domains, which is
dense in each; so each image is contained in the closure of the other, and the
two closures agree. -/
theorem RatMapRep.isDominant_congr {r s : RatMapRep X Y}
    (h : r.Rel s) (hr : r.IsDominant) : s.IsDominant := by
  classical
  -- The image of `r` lies in the closure of the image of `s`: the two agree on
  -- the overlap of the domains, which is dense in `r`'s domain.
  have hopen : IsOpen {y : (X.restrict r.U r.nonempty_U).carrier | y.1 ∈ s.U} :=
    s.U.isOpen.preimage continuous_subtype_val
  have hne : ({y : (X.restrict r.U r.nonempty_U).carrier | y.1 ∈ s.U}).Nonempty := by
    obtain ⟨z, hzr, hzs⟩ :=
      Variety.opens_inter_nonempty (U := r.U) (V := s.U) r.nonempty_U s.nonempty_U
    exact ⟨⟨z, hzr⟩, hzs⟩
  set T : Set Y.carrier :=
    closure (Set.range fun y : (X.restrict s.U s.nonempty_U).carrier => s.hom y) with hT
  have hsubT : {y : (X.restrict r.U r.nonempty_U).carrier | y.1 ∈ s.U}
      ⊆ (fun y : (X.restrict r.U r.nonempty_U).carrier => r.hom y) ⁻¹' T := by
    intro y hy
    have hval : r.hom y = s.hom ⟨y.1, hy⟩ := h y.1 y.2 hy
    show r.hom y ∈ T
    rw [hval]
    exact subset_closure ⟨⟨y.1, hy⟩, rfl⟩
  have hall : ∀ y : (X.restrict r.U r.nonempty_U).carrier, r.hom y ∈ T := by
    have hcl := (isClosed_closure.preimage r.hom.continuous_toFun).closure_subset_iff.2 hsubT
    intro y
    exact hcl ((Variety.dense_of_isOpen_of_nonempty (X := X.restrict r.U r.nonempty_U)
      hopen hne).closure_eq ▸ Set.mem_univ y)
  have hrange : (Set.range fun y : (X.restrict r.U r.nonempty_U).carrier => r.hom y) ⊆ T := by
    rintro _ ⟨y, rfl⟩
    exact hall y
  exact dense_closure.1 (Dense.mono hrange hr)

end Hartshorne
