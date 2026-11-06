/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Hartshorne.Cohomology.ModuleSheavesEnoughInjectives

/-!
# Extensions are classified by `Ext¹`

Hartshorne III, Exercise 6.1. For objects `A` and `B` of an abelian category, an extension of
`B` by `A` is a short exact sequence `0 ⟶ A ⟶ E ⟶ B ⟶ 0`. Two extensions are equivalent when
an isomorphism of their middle objects commutes with both maps. An extension is sent to the
image of `𝟙 B` under the connecting map `Hom(B, B) ⟶ Ext¹(B, A)` of the covariant long exact
sequence, i.e. to its class `ShortComplex.ShortExact.extClass`.

* Injectivity holds in every abelian category with `Ext` groups: two short exact sequences with
  the same class give distinguished triangles in the derived category with the same third
  morphism, hence isomorphic triangles fixing both ends, and the single functor in degree `0` is
  fully faithful.
* Surjectivity uses enough injectives: an embedding `A ⟶ I` into an injective object makes the
  connecting map `Hom(B, I/A) ⟶ Ext¹(B, A)` surjective, and the pullback of `0 ⟶ A ⟶ I ⟶ I/A ⟶ 0`
  along a lift realizes the class.

The result is applied to sheaves of modules on a ringed space and to `𝒪_X`-modules on a scheme,
which have enough injectives (Hartshorne III, Proposition 2.2). No Baer-sum compatibility is
asserted.
-/

open CategoryTheory Limits

universe w w' v u

namespace Hartshorne

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An extension of `B` by `A`: a short exact sequence `0 ⟶ A ⟶ X ⟶ B ⟶ 0`. -/
structure ShortExactExtension (A B : C) where
  /-- The middle object. -/
  X : C
  /-- The monomorphism from `A`. -/
  f : A ⟶ X
  /-- The epimorphism onto `B`. -/
  g : X ⟶ B
  /-- The composition is zero. -/
  zero : f ≫ g = 0
  /-- The sequence is short exact. -/
  shortExact : (ShortComplex.mk f g zero).ShortExact

namespace ShortExactExtension

variable {A B : C}

/-- Two extensions are equivalent when an isomorphism of the middle objects commutes with the
maps from `A` and to `B`. -/
def IsEquivalent (E₁ E₂ : ShortExactExtension A B) : Prop :=
  ∃ e : E₁.X ≅ E₂.X, E₁.f ≫ e.hom = E₂.f ∧ e.hom ≫ E₂.g = E₁.g

/-- The setoid of extensions of `B` by `A` up to equivalence. -/
instance equivalenceSetoid (A B : C) : Setoid (ShortExactExtension A B) where
  r := IsEquivalent
  iseqv := ⟨fun _ => ⟨Iso.refl _, by simp, by simp⟩,
    fun ⟨e, h₁, h₂⟩ => ⟨e.symm, by simp [← h₁], by simp [← h₂]⟩,
    fun ⟨e, h₁, h₂⟩ ⟨e', h₁', h₂'⟩ =>
      ⟨e ≪≫ e', by simp [reassoc_of% h₁, h₁'], by simp [h₂', h₂]⟩⟩

variable [HasExt.{w} C]

/-- The class of an extension: the image of `𝟙 B` under the connecting map
`Hom(B, B) ⟶ Ext¹(B, A)` of the covariant long exact sequence. -/
noncomputable def extClass (E : ShortExactExtension A B) : Abelian.Ext.{w} B A 1 :=
  (Abelian.Ext.mk₀ (𝟙 B)).comp E.shortExact.extClass (zero_add 1)

/-- The class of an extension is the `Ext` class of its short exact sequence. -/
lemma extClass_eq (E : ShortExactExtension A B) : E.extClass = E.shortExact.extClass :=
  Abelian.Ext.mk₀_id_comp _

/-- Equivalent extensions have the same class. -/
lemma extClass_eq_of_isEquivalent {E₁ E₂ : ShortExactExtension A B} (h : E₁ ≈ E₂) :
    E₁.extClass.{w} = E₂.extClass := by
  obtain ⟨e, h₁, h₂⟩ := h
  rw [extClass_eq, extClass_eq]
  have := ShortComplex.ShortExact.extClass_naturality.{w} E₁.shortExact E₂.shortExact
    { τ₁ := 𝟙 A, τ₂ := e.hom, τ₃ := 𝟙 B, comm₁₂ := by simpa using h₁.symm,
      comm₂₃ := by simpa using h₂ }
  simpa [Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id] using this

set_option backward.isDefEq.respectTransparency false in
omit [HasExt.{w} C] in
/-- Extensions with the same connecting morphism in the derived category are equivalent. -/
lemma isEquivalent_of_singleδ_eq [HasDerivedCategory.{w'} C] {E₁ E₂ : ShortExactExtension A B}
    (hδ : E₁.shortExact.singleδ = E₂.shortExact.singleδ) : E₁ ≈ E₂ := by
  let e := Pretriangulated.isoTriangleOfIso₁₃ _ _ E₁.shortExact.singleTriangle_distinguished
    E₂.shortExact.singleTriangle_distinguished (Iso.refl _) (Iso.refl _) (by simpa using hδ)
  let ψ := (DerivedCategory.singleFunctor C 0).preimageIso (Pretriangulated.Triangle.π₂.mapIso e)
  have hψ : (DerivedCategory.singleFunctor C 0).map ψ.hom = e.hom.hom₂ := by
    rw [Functor.preimageIso_hom, Functor.map_preimage]
    rfl
  refine ⟨ψ, ?_, ?_⟩
  · apply (DerivedCategory.singleFunctor C 0).map_injective
    have := e.hom.comm₁
    rw [Functor.map_comp, hψ]
    simpa [e] using this
  · apply (DerivedCategory.singleFunctor C 0).map_injective
    have := e.hom.comm₂
    rw [Functor.map_comp, hψ]
    simpa [e] using this.symm

/-- Extensions with the same class are equivalent. -/
lemma isEquivalent_of_extClass_eq {E₁ E₂ : ShortExactExtension A B}
    (h : E₁.extClass.{w} = E₂.extClass) : E₁ ≈ E₂ := by
  let := HasDerivedCategory.standard C
  rw [extClass_eq, extClass_eq] at h
  apply isEquivalent_of_singleδ_eq
  have := congrArg (fun z => Abelian.Ext.hom z) h
  rw [ShortComplex.ShortExact.extClass_hom, ShortComplex.ShortExact.extClass_hom] at this
  exact this

/-- With enough injectives, every class in `Ext¹(B, A)` is the class of an extension. -/
lemma exists_extClass_eq [EnoughInjectives C] (x : Abelian.Ext.{w} B A 1) :
    ∃ E : ShortExactExtension A B, E.extClass = x := by
  have hS₀ : (ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A))
      (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ (X := B) hS₀ x
    (Abelian.Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨h, rfl⟩ := (Abelian.Ext.mk₀_bijective B _).2 y
  let i : A ⟶ pullback (cokernel.π (Injective.ι A)) h :=
    pullback.lift (Injective.ι A) 0 (by simp)
  have hi₁ : i ≫ pullback.fst _ _ = Injective.ι A := pullback.lift_fst _ _ _
  have hi₂ : i ≫ pullback.snd _ _ = 0 := pullback.lift_snd _ _ _
  have hE : (ShortComplex.mk i (pullback.snd _ _) hi₂).ShortExact := by
    have : Mono i := mono_of_mono_fac hi₁
    refine { exact := ?_ }
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T y hy
    dsimp at y hy
    obtain ⟨T', π, hπ, a, ha⟩ := hS₀.exact.exact_up_to_refinements (y ≫ pullback.fst _ _) (by
      dsimp
      rw [Category.assoc, pullback.condition, reassoc_of% hy, zero_comp])
    refine ⟨T', π, hπ, a, ?_⟩
    dsimp at ha ⊢
    apply pullback.hom_ext
    · rw [Category.assoc, ha, Category.assoc, hi₁]
    · rw [Category.assoc, hy, comp_zero, Category.assoc, hi₂, comp_zero]
  refine ⟨⟨_, i, pullback.snd _ _, hi₂, hE⟩, ?_⟩
  rw [extClass_eq, ← hy]
  have := ShortComplex.ShortExact.extClass_naturality.{w} hE hS₀
    { τ₁ := 𝟙 A, τ₂ := pullback.fst _ _, τ₃ := h, comm₁₂ := by simpa using hi₁.symm,
      comm₂₃ := pullback.condition }
  simpa [Abelian.Ext.comp_mk₀_id] using this

/-- The class map on equivalence classes of extensions of `B` by `A`. -/
noncomputable def quotientExtClass :
    Quotient (equivalenceSetoid A B) → Abelian.Ext.{w} B A 1 :=
  Quotient.lift extClass fun _ _ h => extClass_eq_of_isEquivalent h

/-- In an abelian category with enough injectives, equivalence classes of extensions of `B`
by `A` are in bijection with `Ext¹(B, A)`. -/
theorem quotientExtClass_bijective [EnoughInjectives C] :
    Function.Bijective (quotientExtClass.{w} (A := A) (B := B)) := by
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    exact Quotient.sound (isEquivalent_of_extClass_eq hxy)
  · obtain ⟨E, hE⟩ := exists_extClass_eq x
    exact ⟨⟦E⟧, hE⟩

end ShortExactExtension

/-- **Hartshorne III, Exercise 6.1.** For sheaves of modules `F'` and `F''` on a ringed space,
sending an extension `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` to the image of `𝟙 F''` under the connecting map
induces a bijection from equivalence classes of extensions to `Ext¹(F'', F')`. -/
theorem sheafOfModules_quotientExtClass_bijective (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) [HasExt.{w} (SheafOfModules.{u} R)]
    (F' F'' : SheafOfModules.{u} R) :
    Function.Bijective (ShortExactExtension.quotientExtClass.{w} (A := F') (B := F'')) := by
  have := moduleSheaves_enoughInjectives X R
  exact ShortExactExtension.quotientExtClass_bijective

/-- **Hartshorne III, Exercise 6.1** for `𝒪_X`-modules on a scheme. -/
theorem schemeModules_quotientExtClass_bijective (X : AlgebraicGeometry.Scheme.{u})
    [HasExt.{w} X.Modules] (F' F'' : X.Modules) :
    Function.Bijective (ShortExactExtension.quotientExtClass.{w} (A := F') (B := F'')) := by
  have : EnoughInjectives X.Modules := moduleSheaves_enoughInjectives X X.ringCatSheaf
  exact ShortExactExtension.quotientExtClass_bijective

end Hartshorne
