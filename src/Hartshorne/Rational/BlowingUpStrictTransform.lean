/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.BlowingUpMorphisms

/-!
# Strict transforms under the blow-up of affine space

Hartshorne, *Algebraic Geometry*, I.4, pp. 28–29.

For a closed affine subvariety `Y` through the origin, its blow-up is the
closure, inside the blow-up of affine space, of the inverse image of
`Y \ {0}`.  This file constructs that relative closure, proves that it is
quasi-projective, restricts the ambient blow-up projection to it, and proves
that the projection is an isomorphism away from the exceptional fibre.  Hence,
when `Y \ {0}` is nonempty, the strict transform is birational to `Y`.

The nonemptiness assumption is necessary for the present `Variety` API: a
variety is required to be nonempty, whereas the strict transform of the
zero-dimensional subvariety `{0}` is empty.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {σ : Type u} [Finite σ] [DecidableEq σ] [Nonempty σ]

/-! ## Relative closure inside a locally closed ambient subset -/

/-- The closure of `S ⊆ B`, taken in the subspace `B` but displayed back
in the ambient space. -/
def relativeClosure {X : Type u} [TopologicalSpace X]
    (B : Set X) (S : Set B) : Set X :=
  B ∩ closure ((↑) '' S)

theorem mem_relativeClosure_iff {X : Type u} [TopologicalSpace X]
    {B : Set X} {S : Set B} {x : B} :
    x.1 ∈ relativeClosure B S ↔ x ∈ closure S := by
  rw [relativeClosure, Set.mem_inter_iff]
  constructor
  · intro h
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image S]
    exact h.2
  · intro h
    refine ⟨x.2, ?_⟩
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image S] at h
    exact h

theorem subset_relativeClosure {X : Type u} [TopologicalSpace X]
    {B : Set X} {S : Set B} :
    (↑) '' S ⊆ relativeClosure B S := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x.2, subset_closure ⟨x, hx, rfl⟩⟩

theorem relativeClosure_subset {X : Type u} [TopologicalSpace X]
    {B : Set X} {S : Set B} :
    relativeClosure B S ⊆ B :=
  Set.inter_subset_left

theorem isLocallyClosed_relativeClosure {X : Type u} [TopologicalSpace X]
    {B : Set X} {S : Set B} (hB : IsLocallyClosed B) :
    IsLocallyClosed (relativeClosure B S) := by
  obtain ⟨U, Z, hU, hZ, hBZ⟩ := hB
  refine ⟨U, Z ∩ closure ((↑) '' S), hU,
    hZ.inter isClosed_closure, ?_⟩
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hxB, hxcl⟩
    have hxUZ : x ∈ U ∩ Z := hBZ ▸ hxB
    exact ⟨hxUZ.1, hxUZ.2, hxcl⟩
  · rintro ⟨hxU, hxZ, hxcl⟩
    exact ⟨hBZ.symm ▸ ⟨hxU, hxZ⟩, hxcl⟩

theorem isIrreducible_relativeClosure {X : Type u} [TopologicalSpace X]
    {B : Set X} {S : Set B} (hB : IsLocallyClosed B)
    (hS : IsIrreducible S) : IsIrreducible (relativeClosure B S) := by
  have himage : IsIrreducible ((↑) '' S : Set X) :=
    hS.image ((↑) : B → X) continuous_subtype_val.continuousOn
  obtain ⟨U, Z, hU, hZ, hBZ⟩ := hB
  have hSZ : ((↑) '' S : Set X) ⊆ Z := by
    rintro _ ⟨x, _hx, rfl⟩
    have hxUZ : x.1 ∈ U ∩ Z := hBZ ▸ x.2
    exact hxUZ.2
  have hclZ : closure ((↑) '' S : Set X) ⊆ Z :=
    closure_minimal hSZ hZ
  have heq : relativeClosure B S = closure ((↑) '' S : Set X) ∩ U := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxB, hxcl⟩
      have hxUZ : x ∈ U ∩ Z := hBZ ▸ hxB
      exact ⟨hxcl, hxUZ.1⟩
    · rintro x ⟨hxcl, hxU⟩
      exact ⟨hBZ.symm ▸ ⟨hxU, hclZ hxcl⟩, hxcl⟩
  rw [heq]
  obtain ⟨s, hs⟩ := hS.nonempty
  have hsU : (s.1 : X) ∈ U := by
    have hsUZ : (s.1 : X) ∈ U ∩ Z := hBZ ▸ s.2
    exact hsUZ.1
  exact ⟨⟨s.1, subset_closure ⟨s, hs, rfl⟩, hsU⟩,
    IsPreirreducible.inter_isOpen himage.closure.2 hU⟩

/-! ## Strict transform -/

private noncomputable abbrev strictTransformBlowupQ :
    IsQuasiProjVariety (blowupSet (k := k) (σ := σ)) :=
  isQuasiProjVariety_blowupSet (k := k) (σ := σ)

private noncomputable abbrev strictTransformAffineSpaceQ :
    IsQuasiAffineVariety (Set.univ : Set (σ → k)) :=
  (affineSpace_isAffineVariety (k := k) (σ := σ)).isQuasiAffineVariety

/-- The inverse image of `Y \ {0}` in the blow-up, before closure. -/
def strictTransformOrdinary (Y : Set (σ → k)) :
    Set (blowupSet (k := k) (σ := σ)) :=
  {R | (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ)) R).1 ∈ Y ∧
    (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ)) R).1 ≠ 0}

/-- Hartshorne's strict transform: the relative closure of the inverse image
of `Y \ {0}` inside the blow-up of affine space. -/
def strictTransform (Y : Set (σ → k)) :
    Set (ProjectiveSpace k ((Option σ) × σ)) :=
  relativeClosure (blowupSet (k := k) (σ := σ))
    (strictTransformOrdinary (k := k) Y)

/-- The punctured part of an affine subvariety. -/
def affineSubvarietyPunctured (Y : Set (σ → k)) : Set Y :=
  {x | x.1 ≠ 0}

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
theorem isOpen_affineSubvarietyPunctured
    (Y : Set (σ → k)) : IsOpen (affineSubvarietyPunctured Y) := by
  have hopen (i : σ) : IsOpen {x : Y | x.1 i ≠ 0} := by
    have hc : IsClosed {x : Y | x.1 i = 0} := by
      change IsClosed (Subtype.val ⁻¹' {x : σ → k | x i = 0})
      have hz := (isClosed_zeroSet ({X i} : Set (MvPolynomial σ k))).preimage
        (continuous_subtype_val : Continuous ((↑) : Y → (σ → k)))
      convert hz using 1
      ext x
      simp [mem_zeroSet_iff]
    simpa only [Set.compl_ofPred, not_not] using hc.isOpen_compl
  have heq : affineSubvarietyPunctured Y = ⋃ i : σ, {x : Y | x.1 i ≠ 0} := by
    ext x
    simp only [affineSubvarietyPunctured, Set.mem_ofPred_eq, Set.mem_iUnion]
    exact Function.ne_iff
  rw [heq]
  exact isOpen_iUnion hopen

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
theorem isIrreducible_affineSubvarietyPunctured
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    IsIrreducible (affineSubvarietyPunctured Y) := by
  let _ : IrreducibleSpace Y :=
    isIrreducible_iff_irreducibleSpace.mp hY.1
  refine ⟨hne, ?_⟩
  exact IsPreirreducible.open_subset
    (IrreducibleSpace.isIrreducible_univ (X := Y)).2
    (isOpen_affineSubvarietyPunctured Y) (Set.subset_univ _)

/-- The graph lift `x ↦ (x,[x])` of the punctured subvariety. -/
noncomputable def strictTransformLift (Y : Set (σ → k))
    (x : affineSubvarietyPunctured Y) :
    blowupSet (k := k) (σ := σ) :=
  blowupInverseHom (strictTransformBlowupQ (k := k) (σ := σ))
    ⟨⟨x.1.1, Set.mem_univ _⟩, x.2⟩

theorem continuous_strictTransformLift (Y : Set (σ → k)) :
    Continuous (strictTransformLift (k := k) (σ := σ) Y) := by
  let j : affineSubvarietyPunctured Y →
      ((Variety.ofQuasiAffine
        (strictTransformAffineSpaceQ (k := k) (σ := σ))).restrict
          (affinePuncturedOpen (k := k) (σ := σ))
          (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier :=
    fun x => ⟨⟨x.1.1, Set.mem_univ _⟩, x.2⟩
  have hj : Continuous j :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  exact (blowupInverseHom
    (strictTransformBlowupQ (k := k) (σ := σ))).continuous_toFun.comp hj

theorem range_strictTransformLift (Y : Set (σ → k)) :
    Set.range (strictTransformLift (k := k) (σ := σ) Y) =
      strictTransformOrdinary (k := k) Y := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    have hxne : x.1.1 ≠ 0 := by
      exact x.2
    let z : ((Variety.ofQuasiAffine
        (strictTransformAffineSpaceQ (k := k) (σ := σ))).restrict
          (affinePuncturedOpen (k := k) (σ := σ))
          (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier :=
      ⟨⟨x.1.1, Set.mem_univ _⟩, hxne⟩
    have hlift : strictTransformLift (k := k) (σ := σ) Y x =
        blowupInversePoint (k := k) x.1.1 hxne := by
      change blowupInverseHom
        (strictTransformBlowupQ (k := k) (σ := σ)) z = _
      exact blowupInverseHom_apply
        (strictTransformBlowupQ (k := k) (σ := σ)) z
    have hproj := blowupProjectionAffine_inversePoint
      (strictTransformBlowupQ (k := k) (σ := σ)) x.1.1 hxne
    constructor
    · rw [hlift, hproj]
      exact x.1.2
    · rw [hlift, hproj]
      exact hxne
  · intro R hR
    let x : affineSubvarietyPunctured Y :=
      ⟨⟨(blowupProjectionAffine
        (strictTransformBlowupQ (k := k) (σ := σ)) R).1, hR.1⟩, hR.2⟩
    refine ⟨x, ?_⟩
    let z : ((Variety.ofQuasiAffine
        (strictTransformAffineSpaceQ (k := k) (σ := σ))).restrict
          (affinePuncturedOpen (k := k) (σ := σ))
          (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier :=
      ⟨⟨x.1.1, Set.mem_univ _⟩, x.2⟩
    change blowupInverseHom
      (strictTransformBlowupQ (k := k) (σ := σ)) z = R
    rw [blowupInverseHom_apply]
    exact blowupInversePoint_projection
      (strictTransformBlowupQ (k := k) (σ := σ)) R hR.2

theorem isIrreducible_strictTransformOrdinary
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    IsIrreducible (strictTransformOrdinary (k := k) Y) := by
  let _ : IrreducibleSpace (affineSubvarietyPunctured Y) :=
    isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_affineSubvarietyPunctured hY hne)
  rw [← range_strictTransformLift (k := k) (σ := σ) Y]
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ
      (X := affineSubvarietyPunctured Y)).image
        (strictTransformLift (k := k) (σ := σ) Y)
        (continuous_strictTransformLift (k := k) (σ := σ) Y).continuousOn

theorem isLocallyClosed_strictTransform (Y : Set (σ → k)) :
    IsLocallyClosed (strictTransform (k := k) (σ := σ) Y) :=
  isLocallyClosed_relativeClosure
    (isLocallyClosed_blowupSet (k := k) (σ := σ))

theorem isIrreducible_strictTransform
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    IsIrreducible (strictTransform (k := k) (σ := σ) Y) :=
  isIrreducible_relativeClosure
    (isLocallyClosed_blowupSet (k := k) (σ := σ))
    (isIrreducible_strictTransformOrdinary hY hne)

theorem isQuasiProjVariety_strictTransform
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    IsQuasiProjVariety (strictTransform (k := k) (σ := σ) Y) :=
  isQuasiProjVariety_of_isIrreducible_isLocallyClosed
    (isIrreducible_strictTransform hY hne)
    (isLocallyClosed_strictTransform (k := k) (σ := σ) Y)

theorem strictTransform_subset_blowup (Y : Set (σ → k)) :
    strictTransform (k := k) (σ := σ) Y ⊆
      blowupSet (k := k) (σ := σ) :=
  relativeClosure_subset

theorem strictTransform_projection_mem
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (R : strictTransform (k := k) (σ := σ) Y) :
    (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ))
      ⟨R.1, strictTransform_subset_blowup (k := k) (σ := σ) Y R.2⟩).1 ∈ Y := by
  let B := blowupSet (k := k) (σ := σ)
  let p := blowupProjectionAffine
    (strictTransformBlowupQ (k := k) (σ := σ))
  let C : Set B := {Q | (p Q).1 ∈ Y}
  have hC : IsClosed C := by
    exact hY.2.preimage (continuous_subtype_val.comp p.continuous_toFun)
  have hSC : strictTransformOrdinary (k := k) Y ⊆ C := by
    intro Q hQ
    exact hQ.1
  have hclC : closure (strictTransformOrdinary (k := k) Y) ⊆ C :=
    closure_minimal hSC hC
  exact hclC ((mem_relativeClosure_iff).1 R.2)

/-! ## The restricted projection as a morphism -/

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
theorem affineCoordinate_isGlobalRegular_on
    {Y : Set (σ → k)} (hY : IsQuasiAffineVariety Y) (i : σ) :
    (Variety.ofQuasiAffine hY).IsGlobalRegular (fun y => y.1 i) := by
  intro _
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, X i, 1, by simp, by simp⟩

namespace VarietyHom

variable {A : Variety k} {Y Z : Set (σ → k)}

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
/-- Corestrict a morphism between concretely presented affine varieties when
its image lies in a smaller quasi-affine subset. -/
theorem exists_codRestrictAffine
    (hY : IsQuasiAffineVariety Y) (hZ : IsQuasiAffineVariety Z)
    (f : VarietyHom A (Variety.ofQuasiAffine hY))
    (hf : ∀ x, (f x).1 ∈ Z) :
    ∃ g : VarietyHom A (Variety.ofQuasiAffine hZ),
      g.toFun = fun x => ⟨(f x).1, hf x⟩ := by
  apply (exists_varietyHom_iff_coords_regular hZ
    (fun x => ⟨(f x).1, hf x⟩)).2
  exact (exists_varietyHom_iff_coords_regular hY f.toFun).1 ⟨f, rfl⟩

noncomputable def codRestrictAffine
    (hY : IsQuasiAffineVariety Y) (hZ : IsQuasiAffineVariety Z)
    (f : VarietyHom A (Variety.ofQuasiAffine hY))
    (hf : ∀ x, (f x).1 ∈ Z) :
    VarietyHom A (Variety.ofQuasiAffine hZ) :=
  Classical.choose (exists_codRestrictAffine hY hZ f hf)

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
theorem codRestrictAffine_toFun
    (hY : IsQuasiAffineVariety Y) (hZ : IsQuasiAffineVariety Z)
    (f : VarietyHom A (Variety.ofQuasiAffine hY))
    (hf : ∀ x, (f x).1 ∈ Z) :
    (f.codRestrictAffine hY hZ hf).toFun = fun x => ⟨(f x).1, hf x⟩ :=
  Classical.choose_spec (exists_codRestrictAffine hY hZ f hf)

/-- Inclusion of one concretely presented quasi-affine variety into another. -/
noncomputable def affineIncl
    (hY : IsQuasiAffineVariety Y) (hZ : IsQuasiAffineVariety Z)
    (hYZ : Y ⊆ Z) :
    VarietyHom (Variety.ofQuasiAffine hY) (Variety.ofQuasiAffine hZ) :=
  VarietyHom.ofCoords hZ (fun x => ⟨x.1, hYZ x.2⟩)
    (fun i => by simpa using affineCoordinate_isGlobalRegular_on hY i)

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
theorem affineIncl_toFun
    (hY : IsQuasiAffineVariety Y) (hZ : IsQuasiAffineVariety Z)
    (hYZ : Y ⊆ Z) :
    (affineIncl hY hZ hYZ).toFun = fun x => ⟨x.1, hYZ x.2⟩ := by
  exact VarietyHom.ofCoords_toFun hZ _ _

end VarietyHom

private noncomputable abbrev strictTransformQ
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    IsQuasiProjVariety (strictTransform (k := k) (σ := σ) Y) :=
  isQuasiProjVariety_strictTransform hY hne

/-- Projection of the strict transform to the original affine subvariety. -/
noncomputable def strictTransformProjection
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    VarietyHom
      (Variety.ofQuasiProjective (strictTransformQ hY hne))
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety) :=
  let i : VarietyHom
      (Variety.ofQuasiProjective (strictTransformQ hY hne))
      (Variety.ofQuasiProjective
        (strictTransformBlowupQ (k := k) (σ := σ))) :=
    inclHom (strictTransformBlowupQ (k := k) (σ := σ))
      (strictTransformQ hY hne)
      (strictTransform_subset_blowup (k := k) (σ := σ) Y)
  ((blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ))).comp i).codRestrictAffine
    (strictTransformAffineSpaceQ (k := k) (σ := σ))
    hY.isQuasiAffineVariety
    (strictTransform_projection_mem hY)

theorem strictTransformProjection_apply
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty)
    (R : (Variety.ofQuasiProjective (strictTransformQ hY hne)).carrier) :
    (strictTransformProjection hY hne R).1 =
      (blowupProjectionAffine
        (strictTransformBlowupQ (k := k) (σ := σ))
        ⟨R.1, strictTransform_subset_blowup (k := k) (σ := σ) Y R.2⟩).1 := by
  rw [show (strictTransformProjection hY hne).toFun = _ from
    VarietyHom.codRestrictAffine_toFun
      (strictTransformAffineSpaceQ (k := k) (σ := σ))
      hY.isQuasiAffineVariety _ _]
  rfl

/-- The punctured open subset of `Y`. -/
def affineSubvarietyPuncturedOpen
    {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    Opens (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier where
  carrier := affineSubvarietyPunctured Y
  is_open' := isOpen_affineSubvarietyPunctured Y

/-- The part of the strict transform lying off the exceptional fibre. -/
noncomputable def strictTransformPuncturedOpen
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    Opens (Variety.ofQuasiProjective (strictTransformQ hY hne)).carrier :=
  Opens.comap
    ⟨(strictTransformProjection hY hne).toFun,
      (strictTransformProjection hY hne).continuous_toFun⟩
    (affineSubvarietyPuncturedOpen hY)

theorem blowupProjectionAffine_strictTransformLift
    (Y : Set (σ → k)) (x : affineSubvarietyPunctured Y) :
    (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ))
      (strictTransformLift (k := k) (σ := σ) Y x)).1 = x.1.1 := by
  have hxne : x.1.1 ≠ 0 := x.2
  let z : ((Variety.ofQuasiAffine
      (strictTransformAffineSpaceQ (k := k) (σ := σ))).restrict
        (affinePuncturedOpen (k := k) (σ := σ))
        (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier :=
    ⟨⟨x.1.1, Set.mem_univ _⟩, hxne⟩
  have hlift : strictTransformLift (k := k) (σ := σ) Y x =
      blowupInversePoint (k := k) x.1.1 hxne := by
    change blowupInverseHom
      (strictTransformBlowupQ (k := k) (σ := σ)) z = _
    exact blowupInverseHom_apply
      (strictTransformBlowupQ (k := k) (σ := σ)) z
  rw [hlift]
  exact blowupProjectionAffine_inversePoint
    (strictTransformBlowupQ (k := k) (σ := σ)) x.1.1 hxne

theorem strictTransformPuncturedOpen_nonempty
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    ((strictTransformPuncturedOpen hY hne : Opens
      (Variety.ofQuasiProjective (strictTransformQ hY hne)).carrier) :
      Set (Variety.ofQuasiProjective (strictTransformQ hY hne)).carrier).Nonempty := by
  have hne' := hne
  obtain ⟨x, hx⟩ := hne'
  let xp : affineSubvarietyPunctured Y := ⟨x, hx⟩
  let Q : blowupSet (k := k) (σ := σ) :=
    strictTransformLift (k := k) (σ := σ) Y xp
  have hQord : Q ∈ strictTransformOrdinary (k := k) Y := by
    rw [← range_strictTransformLift (k := k) (σ := σ) Y]
    exact ⟨xp, rfl⟩
  have hQst : Q.1 ∈ strictTransform (k := k) (σ := σ) Y :=
    subset_relativeClosure ⟨Q, hQord, rfl⟩
  let R : (Variety.ofQuasiProjective (strictTransformQ hY hne)).carrier :=
    ⟨Q.1, hQst⟩
  refine ⟨R, ?_⟩
  change (strictTransformProjection hY hne R).1 ≠ 0
  rw [strictTransformProjection_apply]
  change (blowupProjectionAffine
    (strictTransformBlowupQ (k := k) (σ := σ)) Q).1 ≠ 0
  rw [show Q = strictTransformLift (k := k) (σ := σ) Y xp from rfl,
    blowupProjectionAffine_strictTransformLift]
  exact xp.2

/-- Inclusion of the punctured subvariety into punctured affine space. -/
noncomputable def affineSubvarietyPuncturedIncl
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    VarietyHom
      ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
        (affineSubvarietyPuncturedOpen hY) hne)
      ((Variety.ofQuasiAffine
        (strictTransformAffineSpaceQ (k := k) (σ := σ))).restrict
          (affinePuncturedOpen (k := k) (σ := σ))
          (affinePuncturedOpen_nonempty (k := k) (σ := σ))) :=
  let f : VarietyHom
      ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
        (affineSubvarietyPuncturedOpen hY) hne)
      (Variety.ofQuasiAffine
        (strictTransformAffineSpaceQ (k := k) (σ := σ))) :=
    (VarietyHom.affineIncl hY.isQuasiAffineVariety
      (strictTransformAffineSpaceQ (k := k) (σ := σ))
      (Set.subset_univ Y)).comp
        ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).inclHom
          (affineSubvarietyPuncturedOpen hY) hne)
  VarietyHom.liftToRestrict f
    (affinePuncturedOpen (k := k) (σ := σ))
    (affinePuncturedOpen_nonempty (k := k) (σ := σ))
    (fun x => by
      change ((VarietyHom.affineIncl hY.isQuasiAffineVariety
        (strictTransformAffineSpaceQ (k := k) (σ := σ))
        (Set.subset_univ Y)).toFun x.1).1 ≠ 0
      rw [VarietyHom.affineIncl_toFun]
      exact x.2)

theorem affineSubvarietyPuncturedIncl_apply
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty)
    (x : ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
      (affineSubvarietyPuncturedOpen hY) hne).carrier) :
    (affineSubvarietyPuncturedIncl hY hne x).1.1 = x.1.1 := by
  change ((VarietyHom.affineIncl hY.isQuasiAffineVariety
    (strictTransformAffineSpaceQ (k := k) (σ := σ))
    (Set.subset_univ Y)).toFun x.1).1 = x.1.1
  rw [VarietyHom.affineIncl_toFun]

/-- The full blow-up inverse, restricted to punctured points of `Y`. -/
noncomputable def strictTransformInverseToBlowup
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    VarietyHom
      ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
        (affineSubvarietyPuncturedOpen hY) hne)
      (Variety.ofQuasiProjective
        (strictTransformBlowupQ (k := k) (σ := σ))) :=
  (blowupInverseHom
    (strictTransformBlowupQ (k := k) (σ := σ))).comp
      (affineSubvarietyPuncturedIncl hY hne)

theorem strictTransformInverseToBlowup_projection
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty)
    (x : ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
      (affineSubvarietyPuncturedOpen hY) hne).carrier) :
    (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ))
      (strictTransformInverseToBlowup hY hne x)).1 = x.1.1 := by
  let z := affineSubvarietyPuncturedIncl hY hne x
  have hz : z.1.1 = x.1.1 := affineSubvarietyPuncturedIncl_apply hY hne x
  change (blowupProjectionAffine
    (strictTransformBlowupQ (k := k) (σ := σ))
    (blowupInverseHom
      (strictTransformBlowupQ (k := k) (σ := σ)) z)).1 = x.1.1
  rw [blowupInverseHom_apply]
  calc
    (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ))
      (blowupInversePoint (k := k) z.1.1 z.2)).1 = z.1.1 :=
        blowupProjectionAffine_inversePoint
          (strictTransformBlowupQ (k := k) (σ := σ)) z.1.1 z.2
    _ = x.1.1 := hz

theorem strictTransformInverseToBlowup_mem
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty)
    (x : ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
      (affineSubvarietyPuncturedOpen hY) hne).carrier) :
    (strictTransformInverseToBlowup hY hne x).1 ∈
      strictTransform (k := k) (σ := σ) Y := by
  apply subset_relativeClosure
  refine ⟨strictTransformInverseToBlowup hY hne x, ?_, rfl⟩
  constructor
  · rw [strictTransformInverseToBlowup_projection hY hne]
    exact x.1.2
  · rw [strictTransformInverseToBlowup_projection hY hne]
    exact x.2

/-- The inverse away from the origin, corestricted to the strict transform. -/
noncomputable def strictTransformInverse
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    VarietyHom
      ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
        (affineSubvarietyPuncturedOpen hY) hne)
      (Variety.ofQuasiProjective (strictTransformQ hY hne)) :=
  (strictTransformInverseToBlowup hY hne).codRestrictProj
    (strictTransformBlowupQ (k := k) (σ := σ))
    (strictTransformQ hY hne)
    (strictTransformInverseToBlowup_mem hY hne)

theorem strictTransformInverse_forget
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty)
    (x : ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
      (affineSubvarietyPuncturedOpen hY) hne).carrier) :
    (⟨(strictTransformInverse hY hne x).1,
      strictTransform_subset_blowup (k := k) (σ := σ) Y
        (strictTransformInverse hY hne x).2⟩ :
      blowupSet (k := k) (σ := σ)) =
        strictTransformInverseToBlowup hY hne x := by
  apply Subtype.ext
  rw [show (strictTransformInverse hY hne).toFun = _ from
    VarietyHom.codRestrictProj_toFun
      (strictTransformBlowupQ (k := k) (σ := σ))
      (strictTransformQ hY hne)
      (strictTransformInverseToBlowup hY hne)
      (strictTransformInverseToBlowup_mem hY hne)]

theorem strictTransformProjection_inverse
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty)
    (x : ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
      (affineSubvarietyPuncturedOpen hY) hne).carrier) :
    (strictTransformProjection hY hne
      (strictTransformInverse hY hne x)).1 = x.1.1 := by
  rw [strictTransformProjection_apply]
  rw [strictTransformInverse_forget hY hne]
  exact strictTransformInverseToBlowup_projection hY hne x

/-- Projection restricted to the ordinary locus of the strict transform. -/
noncomputable def strictTransformProjectionPunctured
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    VarietyHom
      ((Variety.ofQuasiProjective (strictTransformQ hY hne)).restrict
        (strictTransformPuncturedOpen hY hne)
        (strictTransformPuncturedOpen_nonempty hY hne))
      ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
        (affineSubvarietyPuncturedOpen hY) hne) :=
  VarietyHom.liftToRestrict
    ((strictTransformProjection hY hne).comp
      ((Variety.ofQuasiProjective (strictTransformQ hY hne)).inclHom
        (strictTransformPuncturedOpen hY hne)
        (strictTransformPuncturedOpen_nonempty hY hne)))
    (affineSubvarietyPuncturedOpen hY) hne
    (fun R => R.2)

/-- The inverse map, with codomain restricted to the ordinary locus. -/
noncomputable def strictTransformInversePunctured
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    VarietyHom
      ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
        (affineSubvarietyPuncturedOpen hY) hne)
      ((Variety.ofQuasiProjective (strictTransformQ hY hne)).restrict
        (strictTransformPuncturedOpen hY hne)
        (strictTransformPuncturedOpen_nonempty hY hne)) :=
  VarietyHom.liftToRestrict (strictTransformInverse hY hne)
    (strictTransformPuncturedOpen hY hne)
    (strictTransformPuncturedOpen_nonempty hY hne)
    (fun x => by
      change (strictTransformProjection hY hne
        (strictTransformInverse hY hne x)).1 ≠ 0
      rw [strictTransformProjection_inverse hY hne]
      exact x.2)

theorem strictTransformProjectionPunctured_comp_inverse
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    (strictTransformProjectionPunctured hY hne).comp
      (strictTransformInversePunctured hY hne) =
        VarietyHom.id
          ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).restrict
            (affineSubvarietyPuncturedOpen hY) hne) := by
  apply VarietyHom.ext
  funext x
  apply Subtype.ext
  apply Subtype.ext
  change (strictTransformProjection hY hne
    (strictTransformInverse hY hne x)).1 = x.1.1
  exact strictTransformProjection_inverse hY hne x

theorem strictTransformInverse_comp_projectionPunctured
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    (strictTransformInversePunctured hY hne).comp
      (strictTransformProjectionPunctured hY hne) =
        VarietyHom.id
          ((Variety.ofQuasiProjective (strictTransformQ hY hne)).restrict
            (strictTransformPuncturedOpen hY hne)
            (strictTransformPuncturedOpen_nonempty hY hne)) := by
  apply VarietyHom.ext
  funext R
  let RB : blowupSet (k := k) (σ := σ) :=
    ⟨R.1.1, strictTransform_subset_blowup (k := k) (σ := σ) Y R.1.2⟩
  let x := strictTransformProjectionPunctured hY hne R
  let Q := strictTransformInverseToBlowup hY hne x
  have hRne : (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ)) RB).1 ≠ 0 := by
    have h := R.2
    change (strictTransformProjection hY hne R.1).1 ≠ 0 at h
    rw [strictTransformProjection_apply] at h
    exact h
  have hx : x.1.1 = (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ)) RB).1 := by
    change (strictTransformProjection hY hne R.1).1 = _
    exact strictTransformProjection_apply hY hne R.1
  have hQproj : (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ)) Q).1 = x.1.1 :=
    strictTransformInverseToBlowup_projection hY hne x
  have hQne : (blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ)) Q).1 ≠ 0 := by
    rw [hQproj]
    exact x.2
  have hQinv := blowupInversePoint_projection
    (strictTransformBlowupQ (k := k) (σ := σ)) Q hQne
  have hRinv := blowupInversePoint_projection
    (strictTransformBlowupQ (k := k) (σ := σ)) RB hRne
  let qv : {v : σ → k // v ≠ 0} :=
    ⟨(blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ)) Q).1, hQne⟩
  let rv : {v : σ → k // v ≠ 0} :=
    ⟨(blowupProjectionAffine
      (strictTransformBlowupQ (k := k) (σ := σ)) RB).1, hRne⟩
  have hvec : qv = rv := by
    apply Subtype.ext
    exact hQproj.trans hx
  have hQinv' : blowupInversePoint (k := k) qv.1 qv.2 = Q := hQinv
  have hRinv' : blowupInversePoint (k := k) rv.1 rv.2 = RB := hRinv
  have hmiddle : blowupInversePoint (k := k) qv.1 qv.2 =
      blowupInversePoint (k := k) rv.1 rv.2 :=
    congrArg (fun v : {v : σ → k // v ≠ 0} =>
      blowupInversePoint (k := k) v.1 v.2) hvec
  have hQR : Q = RB := by
    exact hQinv'.symm.trans (hmiddle.trans hRinv')
  apply Subtype.ext
  apply Subtype.ext
  change (strictTransformInverse hY hne x).1 = R.1.1
  have hforget := strictTransformInverse_forget hY hne x
  exact congrArg (fun q : blowupSet (k := k) (σ := σ) => q.1)
    (hforget.trans hQR)

/-- Hartshorne's isomorphism away from the exceptional fibre, for the strict
transform of an affine subvariety. -/
theorem isIso_strictTransformProjectionPunctured
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    (strictTransformProjectionPunctured hY hne).IsIso :=
  ⟨strictTransformInversePunctured hY hne,
    strictTransformInverse_comp_projectionPunctured hY hne,
    strictTransformProjectionPunctured_comp_inverse hY hne⟩

/-- The strict transform of a nontrivial affine subvariety is birational to
the original subvariety. -/
theorem birational_strictTransform
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hne : (affineSubvarietyPunctured Y).Nonempty) :
    Birational
      ⟨Variety.ofQuasiProjective (strictTransformQ hY hne),
        isSeparated_ofQuasiProjective (strictTransformQ hY hne)⟩
      ⟨Variety.ofQuasiAffine hY.isQuasiAffineVariety,
        RationalMapFunctionField.isSeparated_ofQuasiAffine
          hY.isQuasiAffineVariety⟩ := by
  apply (birational_iff_hasIsomorphicOpenSubsets _ _).2
  exact ⟨strictTransformPuncturedOpen hY hne,
    strictTransformPuncturedOpen_nonempty hY hne,
    affineSubvarietyPuncturedOpen hY, hne,
    strictTransformProjectionPunctured hY hne,
    isIso_strictTransformProjectionPunctured hY hne⟩

/-! ## The zero-dimensional edge case -/

/-- If `Y` has no point away from the origin, its ordinary inverse image in the
blow-up is empty. -/
theorem strictTransformOrdinary_eq_empty_of_punctured_not_nonempty
    (Y : Set (σ → k))
    (hne : ¬(affineSubvarietyPunctured Y).Nonempty) :
    strictTransformOrdinary (k := k) Y = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨R, hRY, hR0⟩
  exact hne ⟨⟨(blowupProjectionAffine
    (strictTransformBlowupQ (k := k) (σ := σ)) R).1, hRY⟩, hR0⟩

/-- If `Y` has no point away from the origin, the strict transform defined as
the closure of the inverse image of `Y \ {0}` is empty. -/
theorem strictTransform_eq_empty_of_punctured_not_nonempty
    (Y : Set (σ → k))
    (hne : ¬(affineSubvarietyPunctured Y).Nonempty) :
    strictTransform (k := k) (σ := σ) Y = ∅ := by
  rw [strictTransform,
    strictTransformOrdinary_eq_empty_of_punctured_not_nonempty Y hne]
  simp [relativeClosure]

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
/-- A subvariety containing the origin and having no punctured point is the
singleton origin. -/
theorem eq_singleton_zero_of_punctured_not_nonempty
    (Y : Set (σ → k)) (hzero : (0 : σ → k) ∈ Y)
    (hne : ¬(affineSubvarietyPunctured Y).Nonempty) :
    Y = {0} := by
  apply Set.Subset.antisymm
  · intro y hy
    rw [Set.mem_singleton_iff]
    by_contra hy0
    exact hne ⟨⟨y, hy⟩, hy0⟩
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hzero

/-- Every affine subvariety through the origin has exactly the expected
blow-up behavior. If it has a point away from the origin, its strict transform
is quasi-projective and birational to it, with the projection an isomorphism on
the punctured loci. Otherwise the subvariety is `{0}` and its strict transform
is empty (so it cannot be packaged as a `Variety` in the current API). -/
theorem strictTransform_dichotomy
    {Y : Set (σ → k)} (hY : IsAffineVariety Y)
    (hzero : (0 : σ → k) ∈ Y) :
    (∃ hne : (affineSubvarietyPunctured Y).Nonempty,
      IsQuasiProjVariety (strictTransform (k := k) (σ := σ) Y) ∧
      (strictTransformProjectionPunctured hY hne).IsIso ∧
      Birational
        ⟨Variety.ofQuasiProjective
            (isQuasiProjVariety_strictTransform hY hne),
          isSeparated_ofQuasiProjective
            (isQuasiProjVariety_strictTransform hY hne)⟩
        ⟨Variety.ofQuasiAffine hY.isQuasiAffineVariety,
          RationalMapFunctionField.isSeparated_ofQuasiAffine
            hY.isQuasiAffineVariety⟩) ∨
    (Y = {0} ∧ strictTransform (k := k) (σ := σ) Y = ∅) := by
  classical
  by_cases hne : (affineSubvarietyPunctured Y).Nonempty
  · left
    exact ⟨hne, isQuasiProjVariety_strictTransform hY hne,
      isIso_strictTransformProjectionPunctured hY hne,
      birational_strictTransform hY hne⟩
  · right
    exact ⟨eq_singleton_zero_of_punctured_not_nonempty Y hzero hne,
      strictTransform_eq_empty_of_punctured_not_nonempty
        (k := k) (σ := σ) Y hne⟩

end Hartshorne
