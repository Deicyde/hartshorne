/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.OpenSubvariety
import Hartshorne.Rational.MorphismAgreement
import Mathlib.CategoryTheory.Category.Basic

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
* `Hartshorne.DominantRatMap`, `Hartshorne.SeparatedVariety`
-/

namespace Hartshorne

open TopologicalSpace
open CategoryTheory

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

/-- Dominance as a property of a rational map, independent of the chosen
representative. -/
def RatMap.IsDominant {hY : Y.IsSeparated} (f : RatMap X Y hY) : Prop :=
  Quotient.liftOn f RatMapRep.IsDominant fun r s h => by
    apply propext
    exact ⟨RatMapRep.isDominant_congr h,
      RatMapRep.isDominant_congr (RatMapRep.rel_symm h)⟩

/-- The inverse image of the domain of a second representative is nonempty
when the first representative is dominant. This is the one place where
dominance is needed to define composition. -/
theorem RatMapRep.compDomain_nonempty {Z : Variety.{u, v} k} (s : RatMapRep Y Z)
    (r : RatMapRep X Y) (hr : r.IsDominant) :
    ((Variety.preimageOpens r.nonempty_U r.hom s.U : Opens X.carrier) :
      Set X.carrier).Nonempty := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hr.exists_mem_open s.U.isOpen s.nonempty_U
  refine ⟨x.1, Variety.mem_preimageOpens.2 ⟨x.2, fun h => ?_⟩⟩
  change (s.U : Set Y.carrier) (r.hom ⟨x.1, h⟩)
  have hxeq : (⟨x.1, h⟩ : r.U) = x := Subtype.ext (by rfl)
  rw [hxeq]
  exact hx

/-- Compose representatives of dominant rational maps. The domain is the
inverse image of the domain of the second representative. -/
noncomputable def RatMapRep.comp {Z : Variety.{u, v} k} (s : RatMapRep Y Z)
    (r : RatMapRep X Y) (hr : r.IsDominant) : RatMapRep X Z where
  U := Variety.preimageOpens r.nonempty_U r.hom s.U
  nonempty_U := RatMapRep.compDomain_nonempty s r hr
  hom := s.hom.comp
    (Variety.restrictPreimageHom r.nonempty_U r.hom s.U s.nonempty_U
      (RatMapRep.compDomain_nonempty s r hr))

@[simp]
theorem RatMapRep.comp_eval {Z : Variety.{u, v} k} (s : RatMapRep Y Z)
    (r : RatMapRep X Y) (hr : r.IsDominant) {x : X.carrier}
    (hx : x ∈ Variety.preimageOpens r.nonempty_U r.hom s.U) :
    (s.comp r hr).eval hx =
      s.eval ((Variety.mem_preimageOpens.1 hx).2 (Variety.mem_preimageOpens.1 hx).1) :=
  rfl

/-- A composite of dominant representatives is dominant. -/
theorem RatMapRep.comp_isDominant {Z : Variety.{u, v} k} (s : RatMapRep Y Z)
    (r : RatMapRep X Y) (hs : s.IsDominant) (hr : r.IsDominant) :
    (s.comp r hr).IsDominant := by
  rw [RatMapRep.IsDominant, dense_iff_inter_open]
  intro W hW hWne
  obtain ⟨_, ⟨y, rfl⟩, hyW⟩ := hs.exists_mem_open hW hWne
  let W' : Opens Z.carrier := ⟨W, hW⟩
  let T : Opens Y.carrier :=
    pushOpens s.U (Opens.comap ⟨s.hom.toFun, s.hom.continuous_toFun⟩ W')
  have hTne : (T : Set Y.carrier).Nonempty := by
    refine ⟨y.1, y.2, fun _ => ?_⟩
    exact hyW
  obtain ⟨_, ⟨x, rfl⟩, hxT⟩ := hr.exists_mem_open T.isOpen hTne
  have hxU : r.hom x ∈ s.U := hxT.1
  have hxW : s.hom ⟨r.hom x, hxU⟩ ∈ W := hxT.2 hxU
  let p : (s.comp r hr).U :=
    ⟨x.1, Variety.mem_preimageOpens.2 ⟨x.2, fun h => by
      have hxeq : (⟨x.1, h⟩ : r.U) = x := Subtype.ext (by rfl)
      simpa only [hxeq] using hxU⟩⟩
  refine ⟨s.hom ⟨r.hom x, hxU⟩, hxW, p, ?_⟩
  change s.hom ⟨r.hom ⟨p.1, p.2.1⟩, p.2.2 p.2.1⟩ = s.hom ⟨r.hom x, hxU⟩
  congr

/-- Composition is independent of both representatives. -/
theorem RatMapRep.comp_rel {Z : Variety.{u, v} k} {s s' : RatMapRep Y Z}
    {r r' : RatMapRep X Y} (hs : s.Rel s') (hr : r.Rel r')
    (hdr : r.IsDominant) (hdr' : r'.IsDominant) :
    (s.comp r hdr).Rel (s'.comp r' hdr') := by
  intro x hx hx'
  have hxr : x ∈ r.U := (Variety.mem_preimageOpens.1 hx).1
  have hxr' : x ∈ r'.U := (Variety.mem_preimageOpens.1 hx').1
  have hxs : r.eval hxr ∈ s.U :=
    (Variety.mem_preimageOpens.1 hx).2 hxr
  have hxs' : r'.eval hxr' ∈ s'.U :=
    (Variety.mem_preimageOpens.1 hx').2 hxr'
  have hmid : r.eval hxr = r'.eval hxr' := hr x hxr hxr'
  have hxs'' : r.eval hxr ∈ s'.U := by
    rw [hmid]
    exact hxs'
  rw [RatMapRep.comp_eval s r hdr hx, RatMapRep.comp_eval s' r' hdr' hx']
  calc
    s.eval hxs = s'.eval hxs'' := hs (r.eval hxr) hxs hxs''
    _ = s'.eval hxs' := by
      congr 1

/-- The everywhere-defined identity representative. -/
noncomputable def RatMapRep.id (X : Variety.{u, v} k) : RatMapRep X X where
  U := ⊤
  nonempty_U := Set.univ_nonempty
  hom := Variety.inclHom X ⊤ Set.univ_nonempty

@[simp]
theorem RatMapRep.id_eval (X : Variety.{u, v} k) {x : X.carrier}
    (hx : x ∈ (RatMapRep.id X).U) : (RatMapRep.id X).eval hx = x :=
  rfl

/-- The identity representative is dominant. -/
theorem RatMapRep.id_isDominant (X : Variety.{u, v} k) : (RatMapRep.id X).IsDominant := by
  apply Function.Surjective.denseRange
  intro x
  exact ⟨⟨x, trivial⟩, rfl⟩

/-- Left identity holds up to the representative relation. -/
theorem RatMapRep.id_comp_rel (r : RatMapRep X Y) (hr : r.IsDominant) :
    (RatMapRep.id Y).comp r hr |>.Rel r :=
  fun _ _ _ => rfl

/-- Right identity holds up to the representative relation. -/
theorem RatMapRep.comp_id_rel (r : RatMapRep X Y) :
    (r.comp (RatMapRep.id X) (RatMapRep.id_isDominant X)).Rel r :=
  fun _ _ _ => rfl

/-- Associativity holds up to the representative relation. -/
theorem RatMapRep.comp_assoc_rel {Z W : Variety.{u, v} k} (t : RatMapRep Z W)
    (s : RatMapRep Y Z) (r : RatMapRep X Y) (hs : s.IsDominant) (hr : r.IsDominant) :
    ((t.comp s hs).comp r hr).Rel
      (t.comp (s.comp r hr) (s.comp_isDominant r hs hr)) :=
  fun _ _ _ => rfl

/-- A representative together with the dominance needed for composition. -/
structure DominantRatMapRep (X Y : Variety.{u, v} k) where
  /-- The underlying rational-map representative. -/
  rep : RatMapRep X Y
  /-- Its image is dense. -/
  isDominant : rep.IsDominant

namespace DominantRatMapRep

variable {Z W : Variety.{u, v} k}

/-- Equivalence of dominant representatives is equivalence of the underlying
rational-map representatives. -/
def Rel (r s : DominantRatMapRep X Y) : Prop := r.rep.Rel s.rep

/-- The setoid of dominant representatives. -/
def setoid (X Y : Variety.{u, v} k) (hY : Y.IsSeparated) :
    Setoid (DominantRatMapRep X Y) where
  r := Rel
  iseqv := {
    refl := fun r => r.rep.rel_refl
    symm := fun h => RatMapRep.rel_symm h
    trans := fun h₁ h₂ => RatMapRep.rel_trans hY h₁ h₂ }

/-- Composition of dominant representatives. -/
noncomputable def comp (s : DominantRatMapRep Y Z) (r : DominantRatMapRep X Y) :
    DominantRatMapRep X Z where
  rep := s.rep.comp r.rep r.isDominant
  isDominant := s.rep.comp_isDominant r.rep s.isDominant r.isDominant

theorem comp_rel {s s' : DominantRatMapRep Y Z} {r r' : DominantRatMapRep X Y}
    (hs : Rel s s') (hr : Rel r r') : Rel (s.comp r) (s'.comp r') :=
  RatMapRep.comp_rel hs hr r.isDominant r'.isDominant

/-- The dominant identity representative. -/
noncomputable def id (X : Variety.{u, v} k) : DominantRatMapRep X X :=
  ⟨RatMapRep.id X, RatMapRep.id_isDominant X⟩

end DominantRatMapRep

/-- Dominant rational maps, quotiented by agreement on common domains. -/
def DominantRatMap (X Y : Variety.{u, v} k) (hY : Y.IsSeparated) :=
  Quotient (DominantRatMapRep.setoid X Y hY)

namespace DominantRatMap

variable {Z W : Variety.{u, v} k}

/-- Forget dominance, obtaining the underlying rational map. -/
def toRatMap {hY : Y.IsSeparated} (f : DominantRatMap X Y hY) : RatMap X Y hY :=
  Quotient.map DominantRatMapRep.rep
    (fun {_ _} h => (show RatMapRep.Rel _ _ from h)) f

theorem toRatMap_isDominant {hY : Y.IsSeparated} (f : DominantRatMap X Y hY) :
    (toRatMap f).IsDominant := by
  refine Quotient.inductionOn f ?_
  intro r
  exact r.isDominant

/-- Forgetting dominance loses no information. -/
theorem toRatMap_injective {hY : Y.IsSeparated} :
    Function.Injective (@toRatMap k _ X Y hY) := by
  intro f g
  refine Quotient.inductionOn₂ f g ?_
  intro r s h
  apply Quotient.sound
  change (⟦r.rep⟧ : RatMap X Y hY) = ⟦s.rep⟧ at h
  change r.rep.Rel s.rep
  exact (@Quotient.eq _ (ratMapSetoid X Y hY) r.rep s.rep).1 h

/-- The bundled quotient is equivalent to a rational map equipped with the
well-defined dominance property. -/
noncomputable def equivSubtype {hY : Y.IsSeparated} :
    DominantRatMap X Y hY ≃ {f : RatMap X Y hY // f.IsDominant} :=
  Equiv.ofBijective
    (fun f => ⟨toRatMap f, toRatMap_isDominant f⟩)
    ⟨by
      intro f g h
      apply toRatMap_injective
      exact congrArg Subtype.val h,
     by
      rintro ⟨f, hf⟩
      revert hf
      refine Quotient.inductionOn f ?_
      intro r hr
      exact ⟨⟦⟨r, hr⟩⟧, rfl⟩⟩

/-- Composition of dominant rational maps. -/
noncomputable def comp {hY : Y.IsSeparated} {hZ : Z.IsSeparated}
    (g : DominantRatMap Y Z hZ) (f : DominantRatMap X Y hY) :
    DominantRatMap X Z hZ :=
  Quotient.map₂ DominantRatMapRep.comp
    (fun _ _ hs _ _ hr => DominantRatMapRep.comp_rel hs hr) g f

/-- The identity dominant rational map. -/
noncomputable def id (X : Variety.{u, v} k) (hX : X.IsSeparated) :
    DominantRatMap X X hX := ⟦DominantRatMapRep.id X⟧

@[simp]
theorem comp_id {hX : X.IsSeparated} {hY : Y.IsSeparated}
    (f : DominantRatMap X Y hY) : comp f (id X hX) = f := by
  refine Quotient.inductionOn f ?_
  intro r
  apply Quotient.sound
  exact RatMapRep.comp_id_rel r.rep

@[simp]
theorem id_comp {hY : Y.IsSeparated}
    (f : DominantRatMap X Y hY) : comp (id Y hY) f = f := by
  refine Quotient.inductionOn f ?_
  intro r
  apply Quotient.sound
  exact RatMapRep.id_comp_rel r.rep r.isDominant

theorem assoc {hY : Y.IsSeparated} {hZ : Z.IsSeparated}
    {hW : W.IsSeparated} (f : DominantRatMap X Y hY)
    (g : DominantRatMap Y Z hZ) (h : DominantRatMap Z W hW) :
    comp (comp h g) f = comp h (comp g f) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro r s t
  apply Quotient.sound
  exact RatMapRep.comp_assoc_rel t.rep s.rep r.rep s.isDominant r.isDominant

end DominantRatMap

/-- A variety equipped with the separatedness needed for rational maps to form
a setoid. -/
structure SeparatedVariety (k : Type u) [Field k] where
  /-- The underlying variety. -/
  toVariety : Variety.{u, v} k
  /-- Its separatedness property. -/
  isSeparated : toVariety.IsSeparated

namespace SeparatedVariety

/-- Separated varieties and dominant rational maps form a category. -/
noncomputable instance : Category (SeparatedVariety.{u, v} k) where
  Hom X Y := DominantRatMap X.toVariety Y.toVariety Y.isSeparated
  id X := DominantRatMap.id X.toVariety X.isSeparated
  comp f g := DominantRatMap.comp g f
  id_comp := fun {X _} f => DominantRatMap.comp_id (hX := X.isSeparated) f
  comp_id := fun {_ _} f => DominantRatMap.id_comp f
  assoc := fun {_ _ _ _} f g h => (DominantRatMap.assoc f g h).symm

end SeparatedVariety

end Hartshorne
