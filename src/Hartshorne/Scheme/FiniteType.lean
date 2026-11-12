/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LocallyFiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Morphisms of finite type

Hartshorne, *Algebraic Geometry*, II.3 (p. 84) and Exercise II.3.3(a)–(b) (p. 91).

Hartshorne's finite-cover condition is represented by quasi-compactness, so a
morphism is of finite type when it is locally of finite type and quasi-compact.
-/

namespace Hartshorne

open CategoryTheory

universe u

open AlgebraicGeometry

/-- A morphism of schemes is of finite type when it is locally of finite type
and quasi-compact. This is a proposition, not a competing typeclass for the two
component properties supplied by Mathlib. -/
def FiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyOfFiniteType f ∧ QuasiCompact f

/-- Hartshorne's finite affine-cover formulation of finite type over every
affine open of the target.

For each affine open `U` of the target, the inverse image of `U` has a finite
affine open cover on which the induced coordinate-ring maps are of finite
type. -/
def FiniteTypeOnEveryAffineTarget
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ U : Y.affineOpens,
    ∃ (𝒱 : ((f ⁻¹ᵁ (U : Y.Opens)).toScheme).AffineOpenCover.{u}),
      Finite 𝒱.I₀ ∧
        ∀ j, ((𝒱.openCover.f j ≫ f ∣_ (U : Y.Opens)).appTop).hom.FiniteType

/-- A scheme morphism is of finite type if and only if every affine open of
the target has inverse image admitting a finite affine cover with finite-type
coordinate-ring maps. -/
theorem finiteType_iff_everyAffineTarget
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FiniteType f ↔ FiniteTypeOnEveryAffineTarget f := by
  constructor
  · rintro ⟨hfiniteType, hquasiCompact⟩ U
    obtain ⟨𝒱, h𝒱⟩ :=
      (locallyOfFiniteType_iff_everyAffineTarget f).mp hfiniteType U
    have hcompact : IsCompact (f ⁻¹ᵁ (U : Y.Opens) : Set X) :=
      quasiCompact_iff_forall_isAffineOpen.mp hquasiCompact (U : Y.Opens) U.2
    let _ : CompactSpace ((f ⁻¹ᵁ (U : Y.Opens)).toScheme) :=
      isCompact_iff_compactSpace.mp hcompact
    let 𝒲 : ((f ⁻¹ᵁ (U : Y.Opens)).toScheme).AffineOpenCover.{u} := {
      I₀ := 𝒱.openCover.finiteSubcover.I₀
      X i := 𝒱.X (𝒱.openCover.idx i.1)
      f i := 𝒱.f (𝒱.openCover.idx i.1)
      idx x := 𝒱.openCover.finiteSubcover.idx x
      covers x := 𝒱.openCover.finiteSubcover.covers x
      map_prop i := 𝒱.map_prop (𝒱.openCover.idx i.1) }
    refine ⟨𝒲, ?_, ?_⟩
    · dsimp [𝒲]
      infer_instance
    · intro j
      change
        ((𝒱.openCover.f (𝒱.openCover.idx j.1) ≫
          f ∣_ (U : Y.Opens)).appTop).hom.FiniteType
      exact h𝒱 (𝒱.openCover.idx j.1)
  · intro h
    refine ⟨(locallyOfFiniteType_iff_everyAffineTarget f).mpr ?_,
      quasiCompact_iff_forall_isAffineOpen.mpr ?_⟩
    · intro U
      obtain ⟨𝒱, _, h𝒱⟩ := h U
      exact ⟨𝒱, h𝒱⟩
    · intro U hU
      obtain ⟨𝒱, h𝒱finite, _⟩ := h ⟨U, hU⟩
      let _ : Finite 𝒱.openCover.I₀ := h𝒱finite
      let _ : ∀ i, CompactSpace (𝒱.openCover.X i) := fun i ↦ by
        change CompactSpace (Spec (𝒱.X i))
        infer_instance
      rw [isCompact_iff_compactSpace]
      exact 𝒱.openCover.compactSpace

/-- Hartshorne's definition of a morphism of finite type (II.3, p. 84).

A morphism `f : X ⟶ Y` is of finite type if and only if there is a covering of
`Y` by open affine subsets `V i` such that, for each `i`, the inverse image
`f ⁻¹ᵁ V i` is covered by finitely many open affine subsets `U i j`, each of
whose coordinate rings `Γ(X, U i j)` is a finitely generated `Γ(Y, V i)`-algebra
via the induced map `f.appLE`. -/
theorem finiteType_iff_exists_affine_cover {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FiniteType f ↔
      ∃ (ι : Type u) (V : ι → Y.affineOpens), (⨆ i, (V i : Y.Opens)) = ⊤ ∧
        ∀ i, ∃ (κ : Type u) (_ : Finite κ) (U : κ → X.affineOpens)
          (hU : (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i : Y.Opens)),
          ∀ j, (f.appLE (V i) (U j)
            ((le_iSup (fun j ↦ (U j : X.Opens)) j).trans hU.le)).hom.FiniteType := by
  constructor
  · rintro ⟨hLocallyOfFiniteType, hQuasiCompact⟩
    refine ⟨Y.affineOpens, fun V ↦ V, iSup_affineOpens_eq_top Y, fun V ↦ ?_⟩
    obtain ⟨s, hs, hsV⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (quasiCompact_iff_forall_isAffineOpen.mp hQuasiCompact (V : Y.Opens) V.2)
    refine ⟨s, hs.to_subtype, Subtype.val, ?_, fun j ↦ ?_⟩
    · rw [hsV, iSup_subtype]
    · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f
        hLocallyOfFiniteType _ _ _
  · rintro ⟨ι, V, hV, hU⟩
    choose κ hκ U hUV hUf using hU
    refine ⟨(HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
      (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finiteType_holdsForLocalizationAway).left).mpr fun x ↦ ?_, ?_⟩
    · obtain ⟨i, hi⟩ : ∃ i, f x ∈ (V i : Y.Opens) :=
        TopologicalSpace.Opens.mem_iSup.mp (hV.symm ▸ TopologicalSpace.Opens.mem_top (f x))
      obtain ⟨j, hj⟩ : ∃ j, x ∈ (U i j : X.Opens) :=
        TopologicalSpace.Opens.mem_iSup.mp ((hUV i).symm ▸ hi)
      exact ⟨V i, U i j, hj, _, hUf i j⟩
    · set_option backward.isDefEq.respectTransparency.types false in
      refine (HasAffineProperty.iff_of_iSup_eq_top (P := @QuasiCompact) V hV).mpr
        fun i ↦ ?_
      let _ : Finite (κ i) := hκ i
      refine isCompact_iff_compactSpace.mp
        (show IsCompact (f ⁻¹ᵁ (V i : Y.Opens) : Set X) from ?_)
      rw [← hUV i, TopologicalSpace.Opens.coe_iSup]
      exact isCompact_iUnion fun j ↦ (U i j).2.isCompact

/-- The closed points of a scheme of finite type over a field are dense. -/
theorem closedPoints_dense_of_finiteType
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hf : FiniteType f) : Dense (closedPoints X) := by
  let _ : LocallyOfFiniteType f := hf.1
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  exact dense_iff_closure_eq.mpr closure_closedPoints

/-- Every closed immersion is a morphism of finite type. -/
theorem closedImmersion_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : FiniteType f :=
  ⟨inferInstance, inferInstance⟩

/-- Every quasi-compact open immersion is a morphism of finite type. -/
theorem quasiCompactOpenImmersion_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] [QuasiCompact f] : FiniteType f :=
  ⟨inferInstance, inferInstance⟩

/-- The composite of two morphisms of finite type is of finite type. -/
theorem finiteType_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : FiniteType f) (hg : FiniteType g) : FiniteType (f ≫ g) := by
  let _ : LocallyOfFiniteType f := hf.1
  let _ : LocallyOfFiniteType g := hg.1
  let _ : QuasiCompact f := hf.2
  let _ : QuasiCompact g := hg.2
  exact ⟨locallyOfFiniteType_comp f g, quasiCompact_comp f g⟩

/-- If `f` is quasi-compact and the composite `f ≫ g` is of finite type,
then `f` is of finite type. -/
theorem finiteType_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : QuasiCompact f) (hfg : FiniteType (f ≫ g)) : FiniteType f := by
  let _ : LocallyOfFiniteType (f ≫ g) := hfg.1
  exact ⟨locallyOfFiniteType_of_comp f g, hf⟩

/-- The source of a finite-type morphism to a Noetherian scheme is Noetherian. -/
theorem finiteType_isNoetherian {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian Y] (hf : FiniteType f) : IsNoetherian X := by
  let _ : LocallyOfFiniteType f := hf.1
  let _ : QuasiCompact f := hf.2
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

end Hartshorne
