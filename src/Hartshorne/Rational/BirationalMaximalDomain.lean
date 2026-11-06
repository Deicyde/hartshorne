/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.BirationalMap

/-!
# The maximal domain of a birational transformation

Hartshorne, *Algebraic Geometry*, V.5, the maximal domain of definition and the
fundamental points of a birational transformation, p. 410.

Two representatives of the same rational map agree wherever both are defined,
so all representatives glue to a single morphism on the union of their domains.
That union is the largest open set on which the rational map is a morphism, and
the morphism there is unique. Its closed complement is the fundamental locus,
and the closed points of the fundamental locus are the fundamental points.

The construction uses only that the target is separated, which is how the
project's rational maps are set up; projective varieties are separated by
Lemma I.4.1.

## Main definitions and results

* `Hartshorne.BirationalMap.dom`, `Hartshorne.BirationalMap.domHom`: the maximal
  domain and the glued morphism on it.
* `Hartshorne.BirationalMap.domRep_represents`: that morphism represents `T`.
* `Hartshorne.BirationalMap.domHom_eq_eval`: it restricts to every representative.
* `Hartshorne.BirationalMap.le_dom`, `Hartshorne.BirationalMap.isGreatest_dom`:
  maximality.
* `Hartshorne.BirationalMap.domHom_unique`: uniqueness of the morphism.
* `Hartshorne.BirationalMap.fundamentalLocus`,
  `Hartshorne.BirationalMap.fundamentalPoints`.
-/

namespace Hartshorne

open TopologicalSpace CategoryTheory

universe u v

variable {k : Type u} [Field k]

namespace RatMap

variable {X Y : Variety.{u, v} k} {hY : Y.IsSeparated}

/-- Two representatives of the same rational map agree on their common domain. -/
theorem rel_of_mk_eq {f : RatMap X Y hY} {r s : RatMapRep X Y}
    (hr : Quotient.mk (ratMapSetoid X Y hY) r = f)
    (hs : Quotient.mk (ratMapSetoid X Y hY) s = f) : r.Rel s :=
  Quotient.exact (hr.trans hs.symm)

/-- The union of the domains of all representatives of a rational map. -/
def dom (f : RatMap X Y hY) : Opens X.carrier :=
  ⨆ r : {r : RatMapRep X Y // Quotient.mk (ratMapSetoid X Y hY) r = f}, r.1.U

theorem le_dom {f : RatMap X Y hY} (r : RatMapRep X Y)
    (hr : Quotient.mk (ratMapSetoid X Y hY) r = f) : r.U ≤ f.dom :=
  le_iSup (fun r : {r : RatMapRep X Y // Quotient.mk (ratMapSetoid X Y hY) r = f} => r.1.U)
    ⟨r, hr⟩

theorem mem_dom_iff {f : RatMap X Y hY} {x : X.carrier} :
    x ∈ f.dom ↔ ∃ r : RatMapRep X Y, Quotient.mk (ratMapSetoid X Y hY) r = f ∧ x ∈ r.U := by
  unfold dom
  rw [Opens.mem_iSup]
  constructor
  · rintro ⟨r, hx⟩
    exact ⟨r.1, r.2, hx⟩
  · rintro ⟨r, hr, hx⟩
    exact ⟨⟨r, hr⟩, hx⟩

theorem dom_nonempty (f : RatMap X Y hY) : (f.dom : Set X.carrier).Nonempty := by
  obtain ⟨r, hr⟩ := Quotient.exists_rep f
  obtain ⟨x, hx⟩ := r.nonempty_U
  exact ⟨x, le_dom r hr hx⟩

/-- The glued map on the maximal domain: at each point, the value of any
representative defined there. -/
noncomputable def domFun (f : RatMap X Y hY) (x : f.dom) : Y.carrier :=
  (Classical.choose (mem_dom_iff.1 x.2)).eval (Classical.choose_spec (mem_dom_iff.1 x.2)).2

theorem domFun_eq (f : RatMap X Y hY) {r : RatMapRep X Y}
    (hr : Quotient.mk (ratMapSetoid X Y hY) r = f) (x : f.dom) (hx : x.1 ∈ r.U) :
    f.domFun x = r.eval hx :=
  rel_of_mk_eq (Classical.choose_spec (mem_dom_iff.1 x.2)).1 hr x.1 _ hx

theorem continuous_domFun (f : RatMap X Y hY) : Continuous f.domFun := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨r, hr, hxr⟩ := mem_dom_iff.1 x.2
  let S : Set f.dom := {y | y.1 ∈ r.U}
  have hS : IsOpen S := r.U.isOpen.preimage continuous_subtype_val
  refine ContinuousOn.continuousAt ?_ (hS.mem_nhds hxr)
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : S.domRestrict f.domFun =
      fun y : S => r.hom ⟨y.1.1, y.2⟩ := by
    funext y
    exact domFun_eq f hr y.1 y.2
  rw [heq]
  exact r.hom.continuous_toFun.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

/-- The glued morphism on the maximal domain. -/
noncomputable def domHom (f : RatMap X Y hY) :
    VarietyHom (X.restrict f.dom f.dom_nonempty) Y where
  toFun := f.domFun
  continuous_toFun := f.continuous_domFun
  regular_comp V g hg := by
    refine (X.restrict f.dom f.dom_nonempty).regular_of_locally fun x => ?_
    obtain ⟨r, hr, hxr⟩ := mem_dom_iff.1 x.1.2
    let R : Opens (X.restrict f.dom f.dom_nonempty).carrier :=
      ⟨{y | y.1 ∈ r.U}, r.U.isOpen.preimage continuous_subtype_val⟩
    let W : Opens (X.restrict f.dom f.dom_nonempty).carrier :=
      Opens.comap ⟨f.domFun, f.continuous_domFun⟩ V ⊓ R
    refine ⟨W, inf_le_left, ⟨x.2, hxr⟩, ?_⟩
    have hrg := r.hom.regular_comp V g hg
    rw [Variety.mem_restrict_regular] at hrg ⊢
    have hle : pushOpens f.dom W ≤
        pushOpens r.U (Opens.comap ⟨r.hom.toFun, r.hom.continuous_toFun⟩ V) := by
      intro w hw
      obtain ⟨hwD, hwW⟩ := hw
      obtain ⟨hwV, hwr⟩ := hwW hwD
      refine ⟨hwr, fun h => ?_⟩
      change r.hom ⟨w, h⟩ ∈ V
      have := domFun_eq f hr ⟨w, hwD⟩ h
      rw [RatMapRep.eval] at this
      rw [← this]
      exact hwV
    convert X.regular_restrict hle hrg using 1
    funext w
    congr 1
    apply Subtype.ext
    exact domFun_eq f hr (ofPush w).1 (ofPush w).2.2

theorem domHom_apply (f : RatMap X Y hY) (x : f.dom) : f.domHom x = f.domFun x :=
  rfl

/-- The glued morphism, as a representative. -/
noncomputable def domRep (f : RatMap X Y hY) : RatMapRep X Y :=
  ⟨f.dom, f.dom_nonempty, f.domHom⟩

theorem mk_domRep (f : RatMap X Y hY) :
    Quotient.mk (ratMapSetoid X Y hY) f.domRep = f := by
  obtain ⟨r, hr⟩ := Quotient.exists_rep f
  conv_rhs => rw [← hr]
  apply Quotient.sound
  intro x hd hx
  exact domFun_eq f hr ⟨x, hd⟩ hx

theorem isGreatest_dom (f : RatMap X Y hY) :
    IsGreatest {U | ∃ r : RatMapRep X Y, Quotient.mk (ratMapSetoid X Y hY) r = f ∧ r.U = U}
      f.dom :=
  ⟨⟨f.domRep, f.mk_domRep, rfl⟩, fun _ ⟨r, hr, hU⟩ => hU ▸ le_dom r hr⟩

theorem domHom_unique (f : RatMap X Y hY)
    (φ : VarietyHom (X.restrict f.dom f.dom_nonempty) Y)
    (hφ : Quotient.mk (ratMapSetoid X Y hY) ⟨f.dom, f.dom_nonempty, φ⟩ = f) :
    φ = f.domHom :=
  VarietyHom.ext (funext fun x => (domFun_eq f hφ x x.2).symm)

end RatMap

namespace BirationalMap

variable {X Y : SeparatedVariety.{u, v} k} (T : BirationalMap X Y)

/-- The rational map underlying a birational transformation. -/
abbrev toRatMap : RatMap X.toVariety Y.toVariety Y.isSeparated :=
  DominantRatMap.toRatMap (show DominantRatMap X.toVariety Y.toVariety Y.isSeparated from T.hom)

/-- **Hartshorne V.5, p. 410.** The maximal domain `Dom(T)` of a birational
transformation: the union of the domains of all representatives. -/
def dom : Opens X.toVariety.carrier :=
  (toRatMap T).dom

theorem dom_nonempty : ((dom T : Opens X.toVariety.carrier) : Set X.toVariety.carrier).Nonempty :=
  (toRatMap T).dom_nonempty

/-- **Hartshorne V.5, p. 410.** The morphism on `Dom(T)` obtained by gluing the
representatives of `T`. -/
noncomputable def domHom : VarietyHom (X.toVariety.restrict (dom T) (dom_nonempty T)) Y.toVariety :=
  (toRatMap T).domHom

/-- The glued morphism represents `T`. -/
theorem domRep_represents :
    Quotient.mk (ratMapSetoid X.toVariety Y.toVariety Y.isSeparated)
      ⟨dom T, dom_nonempty T, domHom T⟩ = toRatMap T :=
  (toRatMap T).mk_domRep

/-- The glued morphism agrees with every representative of `T` on its domain. -/
theorem domHom_eq_eval {r : RatMapRep X.toVariety Y.toVariety}
    (hr : Quotient.mk (ratMapSetoid X.toVariety Y.toVariety Y.isSeparated) r = toRatMap T)
    {x : X.toVariety.carrier} (hx : x ∈ r.U) :
    domHom T ⟨x, RatMap.le_dom r hr hx⟩ = r.eval hx :=
  (toRatMap T).domFun_eq hr _ hx

/-- **Maximality.** The domain of every representative of `T` lies in `Dom(T)`. -/
theorem le_dom (r : RatMapRep X.toVariety Y.toVariety)
    (hr : Quotient.mk (ratMapSetoid X.toVariety Y.toVariety Y.isSeparated) r = toRatMap T) :
    r.U ≤ dom T :=
  RatMap.le_dom r hr

/-- `Dom(T)` is the largest open set on which `T` is represented by a morphism. -/
theorem isGreatest_dom :
    IsGreatest {U | ∃ r : RatMapRep X.toVariety Y.toVariety,
      Quotient.mk (ratMapSetoid X.toVariety Y.toVariety Y.isSeparated) r = toRatMap T ∧
        r.U = U} (dom T) :=
  (toRatMap T).isGreatest_dom

/-- **Uniqueness.** A morphism on `Dom(T)` representing `T` is the glued one. -/
theorem domHom_unique (φ : VarietyHom (X.toVariety.restrict (dom T) (dom_nonempty T)) Y.toVariety)
    (hφ : Quotient.mk (ratMapSetoid X.toVariety Y.toVariety Y.isSeparated)
      ⟨dom T, dom_nonempty T, φ⟩ = toRatMap T) :
    φ = domHom T :=
  (toRatMap T).domHom_unique φ hφ

/-- **Hartshorne V.5, p. 410.** The fundamental locus `X \ Dom(T)`, a closed
set. -/
def fundamentalLocus : Closeds X.toVariety.carrier :=
  (dom T).compl

theorem coe_fundamentalLocus :
    (fundamentalLocus T : Set X.toVariety.carrier) = (dom T : Set X.toVariety.carrier)ᶜ :=
  rfl

/-- **Hartshorne V.5, p. 410.** The fundamental points of `T`: the closed points
of its fundamental locus. -/
def fundamentalPoints : Set X.toVariety.carrier :=
  {x | x ∈ fundamentalLocus T ∧ IsClosed ({x} : Set X.toVariety.carrier)}

theorem mem_fundamentalPoints {x : X.toVariety.carrier} :
    x ∈ fundamentalPoints T ↔ x ∉ dom T ∧ IsClosed ({x} : Set X.toVariety.carrier) :=
  Iff.rfl

end BirationalMap

end Hartshorne
