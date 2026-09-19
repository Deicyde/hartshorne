/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.Variety
import Hartshorne.Morphism.Hom

/-!
# An open subset of a variety is a variety

Toward Hartshorne, *Algebraic Geometry*, I.4.

Hartshorne says "`U` is itself a variety" and moves on. He does it in the proof
of Proposition 4.3, again in Theorem 4.4, and again in Corollary 4.5, and
rational maps are not definable without it. This file supplies the
construction.

The content is small and the bookkeeping is not. An open `V ⊆ U ⊆ X` can be read
either as an open subset of `↥U` or as an open subset of `X`, and the two
readings carry the same functions but not the same *types* of function. So the
first half of the file is the dictionary between them: `pushOpens` moves an open
subset of `↥U` down to `X`, and `pushHomeomorph` identifies the two subspaces.
Regularity on the subvariety is then *defined* by transporting along that
identification, which makes all four variety axioms transports of the
corresponding axioms for `X`.

Defining regularity by transport rather than by a fresh local condition is what
keeps this short. It also gives the right answer definitionally: a function on
an open subset of `U` is regular for the subvariety exactly when it is regular
for `X`, which is the statement the rest of §4 uses and which would otherwise
need proving.

## Main definitions

* `Hartshorne.pushOpens`, `Hartshorne.pushHomeomorph`
* `Hartshorne.Variety.restrict`
* `Hartshorne.Variety.inclHom`, `Hartshorne.Variety.inclHomOfLE`
* `Hartshorne.Variety.preimageOpens`, `Hartshorne.Variety.restrictPreimageHom`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

section Push

variable {X : Type*} [TopologicalSpace X] {U : Opens X}

/-- An open subset of the subspace `↥U`, read as an open subset of `X`.

Spelled with a universally quantified proof rather than as an image, so that a
point of the pushed-forward set can be taken apart again without choice. -/
def pushOpens (U : Opens X) (V : Opens ↥U) : Opens X where
  carrier := {x : X | x ∈ U ∧ ∀ h : x ∈ U, (⟨x, h⟩ : ↥U) ∈ V}
  is_open' := by
    have hset : {x : X | x ∈ U ∧ ∀ h : x ∈ U, (⟨x, h⟩ : ↥U) ∈ V}
        = Subtype.val '' (V : Set ↥U) := by
      ext x
      refine ⟨fun hx => ⟨⟨x, hx.1⟩, hx.2 hx.1, rfl⟩, ?_⟩
      rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun _ => hy⟩
    rw [hset]
    exact U.isOpen.isOpenMap_subtype_val _ V.isOpen

theorem mem_pushOpens {V : Opens ↥U} {x : X} :
    x ∈ pushOpens U V ↔ x ∈ U ∧ ∀ h : x ∈ U, (⟨x, h⟩ : ↥U) ∈ V := Iff.rfl

theorem pushOpens_le {V : Opens ↥U} : pushOpens U V ≤ U := fun _ hx => hx.1

theorem pushOpens_mono {V W : Opens ↥U} (h : V ≤ W) : pushOpens U V ≤ pushOpens U W :=
  fun _ hx => ⟨hx.1, fun hU => h (hx.2 hU)⟩

/-- A point of the pushed-forward set, read back inside `↥U`. -/
def ofPush {V : Opens ↥U} (w : pushOpens U V) : V :=
  ⟨⟨w.1, w.2.1⟩, w.2.2 w.2.1⟩

/-- And the other way. -/
def toPush {V : Opens ↥U} (x : V) : pushOpens U V :=
  ⟨x.1.1, x.1.2, fun _ => x.2⟩

@[simp]
theorem ofPush_toPush {V : Opens ↥U} (x : V) : ofPush (toPush x) = x := rfl

@[simp]
theorem toPush_ofPush {V : Opens ↥U} (w : pushOpens U V) : toPush (ofPush w) = w := rfl

/-- The two readings of an open subset of `↥U` are the same space. -/
def pushHomeomorph (U : Opens X) (V : Opens ↥U) : V ≃ₜ pushOpens U V where
  toFun := toPush
  invFun := ofPush
  left_inv := ofPush_toPush
  right_inv := toPush_ofPush
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end Push

variable {k : Type u} [Field k]

namespace Variety

/-- **An open subset of a variety is a variety.**

The carrier is the subspace, and a function on an open subset of it is declared
regular exactly when the same function, read on the ambient space, is. -/
noncomputable def restrict (X : Variety.{u, v} k) (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty) : Variety.{u, v} k where
  carrier := U
  irreducible := by
    have hne : Nonempty ↥(U : Set X.carrier) := hU.to_subtype
    have hpre : PreirreducibleSpace ↥(U : Set X.carrier) :=
      isPreirreducible_iff_preirreducibleSpace.1
        ((PreirreducibleSpace.isPreirreducible_univ (X := X.carrier)).open_subset
          U.isOpen (Set.subset_univ _))
    exact ⟨hne⟩
  regular V := Subalgebra.comap (compAlgHom (ofPush (V := V))) (X.regular (pushOpens U V))
  regular_restrict {V W} hVW {f} hf :=
    X.regular_restrict (pushOpens_mono hVW) hf
  isClosed_zeroLocus {V} {f} hf :=
    (X.isClosed_zeroLocus hf).preimage (pushHomeomorph U V).continuous
  regular_div {V} {f g} hf hg hgne :=
    X.regular_div hf hg fun w => hgne (ofPush w)
  regular_of_locally {V} {f} hloc := by
    refine X.regular_of_locally fun w => ?_
    obtain ⟨W, hWV, hwW, hWreg⟩ := hloc (ofPush w)
    exact ⟨pushOpens U W, pushOpens_mono hWV, ⟨w.2.1, fun _ => hwW⟩, hWreg⟩

theorem mem_restrict_regular {X : Variety.{u, v} k} {U : Opens X.carrier}
    {hU : (U : Set X.carrier).Nonempty} {V : Opens (X.restrict U hU).carrier}
    {f : V → k} :
    f ∈ (X.restrict U hU).regular V
      ↔ (fun w : pushOpens U V => f (ofPush w)) ∈ X.regular (pushOpens U V) :=
  Iff.rfl

/-- **The inclusion of an open subvariety is a morphism.**

Pulling a regular function back along it is restricting it, because the open
sets of the subvariety are open sets of the ambient space. -/
noncomputable def inclHom (X : Variety.{u, v} k) (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty) : VarietyHom (X.restrict U hU) X where
  toFun x := x.1
  continuous_toFun := continuous_subtype_val
  regular_comp V f hf :=
    X.regular_restrict
      (show pushOpens U (Opens.comap ⟨fun x : ↥U => x.1, continuous_subtype_val⟩ V) ≤ V from
        fun _ hx => hx.2 hx.1)
      hf

/-- **And so is the inclusion of a smaller open subvariety into a larger one.** -/
noncomputable def inclHomOfLE (X : Variety.{u, v} k) {V U : Opens X.carrier} (hVU : V ≤ U)
    (hV : (V : Set X.carrier).Nonempty) (hU : (U : Set X.carrier).Nonempty) :
    VarietyHom (X.restrict V hV) (X.restrict U hU) where
  toFun x := ⟨x.1, hVU x.2⟩
  continuous_toFun := (continuous_subtype_val).subtype_mk _
  regular_comp W f hf :=
    X.regular_restrict
      (show pushOpens V (Opens.comap ⟨fun x : ↥V => (⟨x.1, hVU x.2⟩ : ↥U),
          (continuous_subtype_val).subtype_mk _⟩ W) ≤ pushOpens U W from
        fun _ hx => ⟨hVU hx.1, fun _ => hx.2 hx.1⟩)
      hf

/-- The preimage of an open subset of the target under a morphism defined on an
open subvariety, read as an open subset of the ambient space of the source. -/
noncomputable def preimageOpens {A B : Variety.{u, v} k} {U : Opens A.carrier}
    (hU : (U : Set A.carrier).Nonempty) (φ : VarietyHom (A.restrict U hU) B)
    (V : Opens B.carrier) : Opens A.carrier :=
  pushOpens U (Opens.comap ⟨φ.toFun, φ.continuous_toFun⟩ V)

theorem mem_preimageOpens {A B : Variety.{u, v} k} {U : Opens A.carrier}
    {hU : (U : Set A.carrier).Nonempty} {φ : VarietyHom (A.restrict U hU) B}
    {V : Opens B.carrier} {a : A.carrier} :
    a ∈ preimageOpens hU φ V ↔ a ∈ U ∧ ∀ h : a ∈ U, φ ⟨a, h⟩ ∈ V := Iff.rfl

/-- **A morphism out of an open subvariety, cut down to the preimage of an open
subset of the target.**

Both the source and the target shrink, and the point of the construction is that
the source shrinks to an open subvariety of the *ambient* space rather than to a
subvariety of a subvariety. That is what lets composites of rational maps be
represented by a pair `⟨open subset of `X`, morphism⟩` again. -/
noncomputable def restrictPreimageHom {A B : Variety.{u, v} k} {U : Opens A.carrier}
    (hU : (U : Set A.carrier).Nonempty) (φ : VarietyHom (A.restrict U hU) B)
    (V : Opens B.carrier) (hV : (V : Set B.carrier).Nonempty)
    (hP : ((preimageOpens hU φ V : Opens A.carrier) : Set A.carrier).Nonempty) :
    VarietyHom (A.restrict (preimageOpens hU φ V) hP) (B.restrict V hV) where
  toFun x := ⟨φ (ofPush x).1, (ofPush x).2⟩
  continuous_toFun := by
    change Continuous (fun x : preimageOpens hU φ V =>
      (⟨φ ⟨x.1, x.2.1⟩, x.2.2 x.2.1⟩ : V))
    exact (φ.continuous_toFun.comp
      (continuous_subtype_val.subtype_mk (fun x => x.2.1))).subtype_mk _
  regular_comp W f hf :=
    A.regular_restrict
      (show pushOpens (preimageOpens hU φ V)
            (Opens.comap ⟨fun x : preimageOpens hU φ V =>
              ⟨φ ⟨x.1, x.2.1⟩, x.2.2 x.2.1⟩, by
                exact (φ.continuous_toFun.comp
                  (continuous_subtype_val.subtype_mk (fun x => x.2.1))).subtype_mk _⟩ W)
          ≤ pushOpens U (Opens.comap ⟨φ.toFun, φ.continuous_toFun⟩ (pushOpens V W)) from
        fun _ ha => ⟨ha.1.1, fun h => ⟨ha.1.2 h, fun _ => ha.2 ha.1⟩⟩)
      (φ.regular_comp (pushOpens V W) (fun w => f (ofPush w)) hf)

end Variety

end Hartshorne
