/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.ProjVariety

/-!
# Morphisms of varieties

Hartshorne, *Algebraic Geometry*, I.3, the definition on pp. 15-16.

A *morphism* `φ : X → Y` is a continuous map such that for every open `V ⊆ Y`
and every regular `f : V → k`, the composite `f ∘ φ` is regular on `φ⁻¹(V)`.
Composition of morphisms is a morphism, so varieties over `k` form a category.

## Isomorphisms

An isomorphism is a morphism admitting a two-sided inverse **morphism**. That is
not the same as a bijective bicontinuous morphism, and the difference is not a
technicality: Hartshorne's Exercise 3.2 gives two counterexamples, `t ↦ (t², t³)`
onto the cusp `y² = x³`, and the Frobenius `t ↦ tᵖ` in characteristic `p`. Both
are bijective and bicontinuous and neither is an isomorphism.

So `IsIso` is defined here by existence of an inverse morphism, and no lemma
bridges it to bijectivity. That asymmetry is deliberate.

## Main definitions

* `Hartshorne.VarietyHom`, `Hartshorne.VarietyHom.id`, `Hartshorne.VarietyHom.comp`
* `Hartshorne.VarietyHom.IsIso`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k]

/-- Precomposition with a map, as a `k`-algebra homomorphism of function
algebras. -/
def compAlgHom {A B : Type*} (φ : A → B) : (B → k) →ₐ[k] (A → k) where
  toFun g := fun a => g (φ a)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- A morphism of varieties: continuous, and pulling regular functions back to
regular functions. -/
structure VarietyHom (X Y : Variety.{u, v} k) where
  /-- The underlying map. -/
  toFun : X.carrier → Y.carrier
  /-- Which is continuous. -/
  continuous_toFun : Continuous toFun
  /-- And pulls back regular functions to regular functions. -/
  regular_comp : ∀ (V : Opens Y.carrier) (f : V → k), f ∈ Y.regular V →
    (fun x : Opens.comap ⟨toFun, continuous_toFun⟩ V => f ⟨toFun x.1, x.2⟩)
      ∈ X.regular (Opens.comap ⟨toFun, continuous_toFun⟩ V)

namespace VarietyHom

variable {X Y Z : Variety.{u, v} k}

instance : CoeFun (VarietyHom X Y) (fun _ => X.carrier → Y.carrier) := ⟨VarietyHom.toFun⟩

/-- The identity morphism. -/
def id (X : Variety.{u, v} k) : VarietyHom X X where
  toFun := _root_.id
  continuous_toFun := continuous_id
  regular_comp V f hf := hf

/-- Composition of morphisms.

The regularity condition composes because `(g ∘ φ) ∘ ψ = g ∘ (φ ∘ ψ)` and the
comap of opens composes the same way. -/
def comp (g : VarietyHom Y Z) (f : VarietyHom X Y) : VarietyHom X Z where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  regular_comp V h hh :=
    f.regular_comp (Opens.comap ⟨g.toFun, g.continuous_toFun⟩ V) _
      (g.regular_comp V h hh)

@[simp]
theorem id_apply (X : Variety.{u, v} k) (x : X.carrier) : (VarietyHom.id X) x = x := rfl

@[simp]
theorem comp_apply (g : VarietyHom Y Z) (f : VarietyHom X Y) (x : X.carrier) :
    (g.comp f) x = g (f x) := rfl

/-- Two morphisms with the same underlying map are equal. -/
@[ext]
theorem ext {f g : VarietyHom X Y} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; simp_all

theorem comp_id (f : VarietyHom X Y) : f.comp (VarietyHom.id X) = f := ext rfl

theorem id_comp (f : VarietyHom X Y) : (VarietyHom.id Y).comp f = f := ext rfl

theorem comp_assoc {W : Variety.{u, v} k} (h : VarietyHom Z W) (g : VarietyHom Y Z)
    (f : VarietyHom X Y) : (h.comp g).comp f = h.comp (g.comp f) := ext rfl

/-- The map `𝒪(Y) → 𝒪(X)` induced by a morphism `φ : X → Y`.

This is the functoriality that makes `𝒪` an invariant: Proposition 3.5 is stated
in terms of it, and Corollary 3.7 needs it to turn a two-sided inverse of
algebras into a two-sided inverse of morphisms. -/
noncomputable def pullback (f : VarietyHom X Y) : Y.regular ⊤ →ₐ[k] X.regular ⊤ :=
  AlgHom.codRestrict
    ((compAlgHom fun z : (⊤ : Opens X.carrier) => (⟨f z.1, trivial⟩ : (⊤ : Opens Y.carrier))).comp
      (Y.regular ⊤).val)
    (X.regular ⊤)
    fun g => f.regular_comp ⊤ g.1 g.2

@[simp]
theorem pullback_val (f : VarietyHom X Y) (g : Y.regular ⊤) (z : (⊤ : Opens X.carrier)) :
    (f.pullback g).val z = g.val ⟨f z.1, trivial⟩ :=
  rfl

@[simp]
theorem pullback_id (X : Variety.{u, v} k) :
    (VarietyHom.id X).pullback = AlgHom.id k (X.regular ⊤) := by
  ext g z
  rfl

/-- Pullback is contravariantly functorial. -/
theorem pullback_comp (g : VarietyHom Y Z) (f : VarietyHom X Y) :
    (g.comp f).pullback = f.pullback.comp g.pullback := by
  ext h z
  rfl

/-- An *isomorphism* is a morphism admitting a two-sided inverse morphism.

Deliberately **not** defined as a bijective bicontinuous morphism: Exercise 3.2
shows those are strictly weaker. -/
def IsIso (f : VarietyHom X Y) : Prop :=
  ∃ g : VarietyHom Y X, g.comp f = VarietyHom.id X ∧ f.comp g = VarietyHom.id Y

theorem isIso_id (X : Variety.{u, v} k) : IsIso (VarietyHom.id X) :=
  ⟨VarietyHom.id X, comp_id _, comp_id _⟩

theorem IsIso.comp {g : VarietyHom Y Z} {f : VarietyHom X Y}
    (hg : IsIso g) (hf : IsIso f) : IsIso (g.comp f) := by
  obtain ⟨g', hg₁, hg₂⟩ := hg
  obtain ⟨f', hf₁, hf₂⟩ := hf
  refine ⟨f'.comp g', ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc g' g f, hg₁, id_comp, hf₁]
  · rw [comp_assoc, ← comp_assoc f f' g', hf₂, id_comp, hg₂]

/-- An isomorphism is in particular bijective. The converse fails; see the note
on Exercise 3.2. -/
theorem IsIso.bijective {f : VarietyHom X Y} (hf : IsIso f) : Function.Bijective f := by
  obtain ⟨g, h₁, h₂⟩ := hf
  constructor
  · intro a b hab
    have := congrArg (fun (φ : VarietyHom X X) => φ.toFun a) h₁
    have hb := congrArg (fun (φ : VarietyHom X X) => φ.toFun b) h₁
    simp only [comp_apply, id_apply] at this hb
    rw [← this, ← hb, hab]
  · intro y
    refine ⟨g y, ?_⟩
    have := congrArg (fun (φ : VarietyHom Y Y) => φ.toFun y) h₂
    simpa using this

end VarietyHom

end Hartshorne
