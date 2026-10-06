/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sets.Closeds

/-!
# The generic-completion functor

Hartshorne, *Algebraic Geometry*, II.2, Proposition 2.6, p. 78.
-/

noncomputable section

open CategoryTheory Set TopologicalSpace

namespace Hartshorne

universe u

/-- The open of the generic completion corresponding to an open `U` of `X`. -/
def genericCompletionOpen (X : TopCat.{u}) (U : Opens X) :
    Set (IrreducibleCloseds X) :=
  { Z | ((Z : Set X) ∩ U).Nonempty }

private lemma genericCompletionOpen_top (X : TopCat.{u}) :
    genericCompletionOpen X ⊤ = Set.univ := by
  ext Z
  simp only [genericCompletionOpen, Opens.coe_top, Set.inter_univ, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  exact Z.isIrreducible.nonempty

private lemma genericCompletionOpen_inf (X : TopCat.{u}) (U V : Opens X) :
    genericCompletionOpen X (U ⊓ V) =
      genericCompletionOpen X U ∩ genericCompletionOpen X V := by
  ext Z
  constructor
  · intro h
    change ((Z : Set X) ∩ ((U : Set X) ∩ V)).Nonempty at h
    exact ⟨h.mono (fun _ hx ↦ ⟨hx.1, hx.2.1⟩),
      h.mono (fun _ hx ↦ ⟨hx.1, hx.2.2⟩)⟩
  · rintro ⟨hU, hV⟩
    change ((Z : Set X) ∩ ((U : Set X) ∩ V)).Nonempty
    exact Z.isIrreducible.isPreirreducible U V U.isOpen V.isOpen hU hV

private lemma genericCompletionOpen_iSup
    (X : TopCat.{u}) {ι : Type*} (U : ι → Opens X) :
    genericCompletionOpen X (⨆ i, U i) =
      ⋃ i, genericCompletionOpen X (U i) := by
  ext Z
  simp only [genericCompletionOpen, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hxZ, hxU⟩
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxU
    exact ⟨i, x, hxZ, hxi⟩
  · rintro ⟨i, x, hxZ, hxi⟩
    exact ⟨x, hxZ, Opens.mem_iSup.mpr ⟨i, hxi⟩⟩

/-- Hartshorne's topology on the irreducible closed subsets of `X`. -/
@[reducible] def genericCompletionTopology (X : TopCat.{u}) :
    TopologicalSpace (IrreducibleCloseds X) where
  IsOpen s := ∃ U : Opens X, s = genericCompletionOpen X U
  isOpen_univ := ⟨⊤, (genericCompletionOpen_top X).symm⟩
  isOpen_inter s t := by
    rintro ⟨U, rfl⟩ ⟨V, rfl⟩
    exact ⟨U ⊓ V, (genericCompletionOpen_inf X U V).symm⟩
  isOpen_sUnion s hs := by
    classical
    choose U hU using fun t : s ↦ hs t.1 t.2
    refine ⟨⨆ t : s, U t, ?_⟩
    rw [genericCompletionOpen_iSup]
    ext Z
    simp only [Set.mem_sUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨t, hts, hZt⟩
      let t' : s := ⟨t, hts⟩
      refine ⟨t', ?_⟩
      rw [← hU t']
      exact hZt
    · rintro ⟨t, hZt⟩
      refine ⟨t.1, t.2, ?_⟩
      rw [hU t]
      exact hZt

/-- The generic completion of a topological space. -/
def genericCompletionObj (X : TopCat.{u}) : TopCat.{u} :=
  @TopCat.of (IrreducibleCloseds X) (genericCompletionTopology X)

private lemma irreducibleCloseds_map_id (X : TopCat.{u})
    (Z : IrreducibleCloseds X) :
    IrreducibleCloseds.map id continuous_id Z = Z := by
  apply IrreducibleCloseds.ext
  simp [IrreducibleCloseds.map, Z.isClosed.closure_eq]

private lemma irreducibleCloseds_map_comp
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : IrreducibleCloseds X) :
    IrreducibleCloseds.map g g.hom.continuous
        (IrreducibleCloseds.map f f.hom.continuous T) =
      IrreducibleCloseds.map (g ∘ f)
        (g.hom.continuous.comp f.hom.continuous) T := by
  apply IrreducibleCloseds.ext
  change closure (g '' closure (f '' (T : Set X))) =
    closure ((g ∘ f) '' (T : Set X))
  apply le_antisymm
  · apply closure_minimal
    · simpa [Set.image_image, Function.comp_def] using
        (image_closure_subset_closure_image g.hom.continuous (s := f '' (T : Set X)))
    · exact isClosed_closure
  · apply closure_mono
    simpa [Set.image_image, Function.comp_def] using
      (Set.image_mono subset_closure :
        g '' (f '' (T : Set X)) ⊆ g '' closure (f '' (T : Set X)))

private lemma genericCompletionOpen_preimage
    {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Opens Y) :
    (IrreducibleCloseds.map f f.hom.continuous) ⁻¹'
        genericCompletionOpen Y U =
      genericCompletionOpen X ((Opens.map f).obj U) := by
  ext Z
  change (closure (f '' (Z : Set X)) ∩ (U : Set Y)).Nonempty ↔
    ((Z : Set X) ∩ f ⁻¹' (U : Set Y)).Nonempty
  rw [closure_inter_open_nonempty_iff U.isOpen]
  constructor
  · rintro ⟨_, ⟨x, hxZ, rfl⟩, hfxU⟩
    exact ⟨x, hxZ, hfxU⟩
  · rintro ⟨x, hxZ, hfxU⟩
    exact ⟨f x, ⟨x, hxZ, rfl⟩, hfxU⟩

/-- The map on generic completions induced by a continuous map. -/
def genericCompletionMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    genericCompletionObj X ⟶ genericCompletionObj Y := by
  letI := genericCompletionTopology X
  letI := genericCompletionTopology Y
  exact TopCat.ofHom
    ⟨IrreducibleCloseds.map f f.hom.continuous, by
      rw [continuous_def]
      rintro s ⟨U, rfl⟩
      exact ⟨(Opens.map f).obj U, genericCompletionOpen_preimage f U⟩⟩

/-- Hartshorne's generic-completion functor. -/
def genericCompletionFunctor : TopCat.{u} ⥤ TopCat.{u} where
  obj := genericCompletionObj
  map := genericCompletionMap
  map_id X := by
    ext Z
    change IrreducibleCloseds.map id continuous_id Z = Z
    exact irreducibleCloseds_map_id X Z
  map_comp f g := by
    ext Z
    change IrreducibleCloseds.map (g ∘ f)
        (g.hom.continuous.comp f.hom.continuous) Z =
      IrreducibleCloseds.map g g.hom.continuous
        (IrreducibleCloseds.map f f.hom.continuous Z)
    exact (irreducibleCloseds_map_comp f g Z).symm

/-- The point of the generic completion associated to `x`. -/
def genericCompletionAlphaPoint (X : TopCat.{u}) (x : X) :
    IrreducibleCloseds X where
  carrier := closure {x}
  isIrreducible' := isIrreducible_singleton.closure
  isClosed' := isClosed_closure

private lemma genericCompletionAlphaPoint_mem_open_iff
    (X : TopCat.{u}) (U : Opens X) (x : X) :
    genericCompletionAlphaPoint X x ∈ genericCompletionOpen X U ↔ x ∈ U := by
  change (closure ({x} : Set X) ∩ (U : Set X)).Nonempty ↔ x ∈ U
  rw [closure_inter_open_nonempty_iff U.isOpen]
  simp

private lemma genericCompletionAlphaPoint_preimage
    (X : TopCat.{u}) (U : Opens X) :
    genericCompletionAlphaPoint X ⁻¹' genericCompletionOpen X U = U := by
  ext x
  exact genericCompletionAlphaPoint_mem_open_iff X U x

/-- The canonical map `x ↦ closure {x}` into the generic completion. -/
def genericCompletionAlpha (X : TopCat.{u}) :
    X ⟶ genericCompletionObj X := by
  letI := genericCompletionTopology X
  exact TopCat.ofHom
    ⟨genericCompletionAlphaPoint X, by
      rw [continuous_def]
      rintro s ⟨U, rfl⟩
      rw [genericCompletionAlphaPoint_preimage]
      exact U.isOpen⟩

/-- The open subsets of `X` and its generic completion are canonically order
isomorphic. -/
def genericCompletionOpensOrderIso (X : TopCat.{u}) :
    Opens X ≃o Opens (genericCompletionObj X) := by
  letI := genericCompletionTopology X
  refine
    { toFun := fun U ↦ ⟨genericCompletionOpen X U, ⟨U, rfl⟩⟩
      invFun := fun V ↦ (Opens.map (genericCompletionAlpha X)).obj V
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · intro U
    apply Opens.ext
    exact genericCompletionAlphaPoint_preimage X U
  · intro V
    obtain ⟨U, hVU⟩ := V.isOpen
    let V' : Set (IrreducibleCloseds X) := V.1
    have hVU' : V' = genericCompletionOpen X U := hVU
    have hpre : (Opens.map (genericCompletionAlpha X)).obj V = U := by
      apply Opens.ext
      change genericCompletionAlphaPoint X ⁻¹' V' = (U : Set X)
      rw [hVU', genericCompletionAlphaPoint_preimage]
    apply Opens.ext
    change genericCompletionOpen X
        ((Opens.map (genericCompletionAlpha X)).obj V) = V'
    rw [hpre, hVU']
  · intro U V
    constructor
    · intro h x hx
      have hx' : genericCompletionAlphaPoint X x ∈ genericCompletionOpen X U :=
        (genericCompletionAlphaPoint_mem_open_iff X U x).mpr hx
      exact (genericCompletionAlphaPoint_mem_open_iff X V x).mp (h hx')
    · intro h Z hZ
      exact hZ.mono (fun _ hx ↦ ⟨hx.1, h hx.2⟩)

private lemma genericCompletionOpen_compl (X : TopCat.{u}) (U : Opens X) :
    (genericCompletionOpen X U)ᶜ =
      { Z : IrreducibleCloseds X | (Z : Set X) ⊆ (U : Set X)ᶜ } := by
  ext Z
  constructor
  · intro h z hzZ hzU
    exact h ⟨z, hzZ, hzU⟩
  · intro h hne
    obtain ⟨z, hzZ, hzU⟩ := hne
    exact h hzZ hzU

/-- The closed subsets of the generic completion are exactly Hartshorne's
sets `t(C) = {Z | Z ⊆ C}` for closed `C ⊆ X`. -/
theorem genericCompletion_isClosed_iff
    (X : TopCat.{u}) (S : Set (IrreducibleCloseds X)) :
    @IsClosed _ (genericCompletionTopology X) S ↔ ∃ C : Set X, IsClosed C ∧
      S = { Z : IrreducibleCloseds X | (Z : Set X) ⊆ C } := by
  let _ := genericCompletionTopology X
  rw [← isOpen_compl_iff]
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl, ?_⟩
    calc
      S = Sᶜᶜ := (compl_compl S).symm
      _ = (genericCompletionOpen X U)ᶜ := congrArg (·ᶜ) hU
      _ = _ := genericCompletionOpen_compl X U
  · rintro ⟨C, hC, rfl⟩
    let U : Opens X := ⟨Cᶜ, hC.isOpen_compl⟩
    refine ⟨U, ?_⟩
    apply compl_injective
    rw [compl_compl, genericCompletionOpen_compl]
    simp only [U, Opens.coe_mk, compl_compl]

end Hartshorne
