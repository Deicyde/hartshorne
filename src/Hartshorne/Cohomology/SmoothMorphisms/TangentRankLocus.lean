/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.SmoothTangentCriterion
import Hartshorne.Scheme.Differentials.DenseNonsingularLocus
import Hartshorne.Scheme.ReducedInducedSubscheme
import Mathlib.Topology.Constructible

/-!
# Constructible tangent-rank loci

Hartshorne, *Algebraic Geometry*, III, the rank loci in the proof of Proposition 10.6 (p. 272).

Let `f : X → Y` be a morphism of schemes of finite type over an algebraically closed field `k`.
For an integer `r`, the closed points `x ∈ X` at which the Zariski tangent map
`T_x X → k(x) ⊗ T_{f x} Y` has rank at most `r` are the closed points of a constructible subset
of `X`.

## Main results

* `Hartshorne.TangentRank.finrank_range_zariskiTangentMap`: the rank of the tangent map is the
  rank of the scalar-extended cotangent map `k(x) ⊗ 𝔪_y/𝔪_y² → 𝔪_x/𝔪_x²`.
* `Hartshorne.TangentRank.moduleFiberDim_add_finrank_range_zariskiTangentMap`: at a closed point
  `x`, `dim Ω_{X/Y} ⊗ k(x) + rank (T_x f) = dim Ω_{X/k} ⊗ k(x)`.
* `Hartshorne.TangentRank.isConstructible_setOf_moduleFiberDim_le`: the set of points where
  `dim Ω_{X/k} ⊗ k(x) ≤ dim Ω_{X/Y} ⊗ k(x) + r` is constructible.
* `Hartshorne.TangentRank.exists_isConstructible_tangentRank_le`: the closed points at which the
  tangent map has rank at most `r` are the closed points of a constructible set.

## Proof

At a closed point `x` with `y = f x`, the residue field of `x` is `k`. The fibre at `x` of the
exact sequence `f^*Ω_{Y/k} → Ω_{X/k} → Ω_{X/Y} → 0` is, after the identification
`Ω_{X/k} ⊗ k(x) ≅ 𝔪_x/𝔪_x²` of II.8.7, the exact sequence
`k(x) ⊗ 𝔪_y/𝔪_y² → 𝔪_x/𝔪_x² → Ω_{X/Y} ⊗ k(x) → 0`. The tangent map is the dual of the first
map, so its rank is `dim Ω_{X/k} ⊗ k(x) - dim Ω_{X/Y} ⊗ k(x)`. Both fibre dimensions are upper
semicontinuous functions of `x` (the sheaves are coherent), and the first is bounded on the
quasi-compact scheme `X`. So the set where `dim Ω_{X/k} ⊗ k(x) ≤ dim Ω_{X/Y} ⊗ k(x) + r` is a
finite union of locally closed sets, which is constructible in the Noetherian space `X`, and its
closed points are those where the tangent map has rank at most `r`.
-/

namespace Hartshorne

-- A definitionally equal duplicate of `schemeModulesStalkModule`, the instance used by
-- `moduleFiberDim`; erased so that the fibre-dimension lemmas apply syntactically.
attribute [-instance] moduleSheafStalkModule

noncomputable section

open IsLocalRing Module KaehlerDifferential CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct

universe u

namespace TangentRank

section Rank

variable {X Y : Scheme.{u}}

/-- The rank of the Zariski tangent map `T_x X → k(x) ⊗_{k(y)} T_y Y` is the rank of the
scalar-extended cotangent map `k(x) ⊗_{k(y)} 𝔪_y/𝔪_y² → 𝔪_x/𝔪_x²`, of which it is the dual. -/
theorem finrank_range_zariskiTangentMap (f : X ⟶ Y) (x : X)
    [Module.Finite (ResidueField (Y.presheaf.stalk (f x)))
      (CotangentSpace (Y.presheaf.stalk (f x)))] :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI := isLocalHom_stalkMap_algebraMap f x
    finrank (ResidueField (X.presheaf.stalk x)) (LinearMap.range (zariskiTangentMap f x)) =
      finrank (ResidueField (X.presheaf.stalk x))
        (LinearMap.range
          (localCotangentBaseChange (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))) := by
  let _ := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f x
  have h : zariskiTangentMap f x = (dualBaseChangeEquiv _ _ _).symm.toLinearMap ∘ₗ
      (localCotangentBaseChange (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)).dualMap := rfl
  rw [h, LinearMap.range_comp, LinearEquiv.finrank_map_eq,
    LinearMap.finrank_range_dualMap_eq_finrank_range]

end Rank

section ClosedPoint

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Over (Spec (CommRingCat.of k))}

/-- **The rank of the tangent map at a closed point.** Let `f : X ⟶ Y` be a morphism of schemes
locally of finite type over an algebraically closed field `k`, and let `x` be a closed point of
`X`. Then `dim Ω_{X/Y} ⊗ k(x) + rank (T_x X → k(x) ⊗ T_{f x} Y) = dim Ω_{X/k} ⊗ k(x)`.

This is the dimension count in the fibre at `x` of the exact sequence
`f^*Ω_{Y/k} → Ω_{X/k} → Ω_{X/Y} → 0` of II.8.11, identified by II.8.7 with the cotangent
sequence `k(x) ⊗ 𝔪_{f x}/𝔪_{f x}² → 𝔪_x/𝔪_x² → Ω_{X/Y} ⊗ k(x) → 0`. -/
theorem moduleFiberDim_add_finrank_range_zariskiTangentMap [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    moduleFiberDim (Scheme.relativeDifferentials f.left) x +
        finrank (ResidueField (X.left.presheaf.stalk x))
          (LinearMap.range (zariskiTangentMap f.left x)) =
      moduleFiberDim (Scheme.relativeDifferentials X.hom) x := by
  have := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let _ := (f.left.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_algebraMap f.left x
  let eA := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of k), ⊤) := (eA.toMulEquiv.isField (Field.toIsField k)).toField
  let : Algebra Γ(Spec (.of k), ⊤) (Y.left.presheaf.stalk (f.left x)) :=
    (Y.hom.appTop ≫ Y.left.presheaf.germ ⊤ (f.left x) trivial).hom.toAlgebra
  let : Algebra Γ(Spec (.of k), ⊤) (X.left.presheaf.stalk x) :=
    (X.hom.appTop ≫ X.left.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : IsScalarTower Γ(Spec (.of k), ⊤) (Y.left.presheaf.stalk (f.left x))
      (X.left.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change X.left.presheaf.germ ⊤ x trivial (X.hom.appTop c) =
      f.left.stalkMap x (Y.left.presheaf.germ ⊤ (f.left x) trivial (Y.hom.appTop c))
    rw [← Over.w f]
    exact (Scheme.Hom.germ_stalkMap_apply f.left ⊤ x trivial (Y.hom.appTop c)).symm
  -- `k → κ(x)` is bijective at the closed point `x`
  have hk : Function.Bijective
      (algebraMap Γ(Spec (.of k), ⊤) (ResidueField (X.left.presheaf.stalk x))) :=
    SmoothTangent.bijective_residue_germ_appTop X.hom x hx
  have hex : Function.Exact
      (mapBaseChange Γ(Spec (.of k), ⊤) (Y.left.presheaf.stalk (f.left x))
        (X.left.presheaf.stalk x))
      (map Γ(Spec (.of k), ⊤) (Y.left.presheaf.stalk (f.left x)) (X.left.presheaf.stalk x)
        (X.left.presheaf.stalk x)) := by
    -- the stalk at `x` of the exact sequence of II.8.11 for `X ⟶ Y ⟶ Spec k`, over the stalk `S₀`
    -- of `Spec k`, and then over `k` itself
    let S₀ := (Spec (.of k)).presheaf.stalk (Y.hom (f.left x))
    let _ : Algebra S₀ (Y.left.presheaf.stalk (f.left x)) :=
      (Y.hom.stalkMap (f.left x)).hom.toAlgebra
    let _ : Algebra S₀ (X.left.presheaf.stalk x) :=
      ((f.left.stalkMap x).hom.comp (Y.hom.stalkMap (f.left x)).hom).toAlgebra
    have : IsScalarTower S₀ (Y.left.presheaf.stalk (f.left x)) (X.left.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let p : (⊤ : (Spec (.of k)).Opens) := ⟨Y.hom (f.left x), trivial⟩
    let : Algebra Γ(Spec (.of k), ⊤) S₀ :=
      TopCat.Presheaf.algebra_section_stalk (Spec (.of k)).presheaf p
    have : IsLocalization.AtPrime S₀ ((isAffineOpen_top (Spec (.of k))).primeIdealOf p).asIdeal :=
      (isAffineOpen_top (Spec (.of k))).isLocalization_stalk p
    have : Algebra.FormallyUnramified Γ(Spec (.of k), ⊤) S₀ :=
      Algebra.FormallyUnramified.of_isLocalization
        ((isAffineOpen_top (Spec (.of k))).primeIdealOf p).asIdeal.primeCompl
    have hY : ∀ c : Γ(Spec (.of k), ⊤), Y.hom.stalkMap (f.left x)
        ((Spec (.of k)).presheaf.germ ⊤ (Y.hom (f.left x)) trivial c) =
          Y.left.presheaf.germ ⊤ (f.left x) trivial (Y.hom.appTop c) := fun c ↦
      Scheme.Hom.germ_stalkMap_apply Y.hom ⊤ (f.left x) trivial c
    have : IsScalarTower Γ(Spec (.of k), ⊤) S₀ (Y.left.presheaf.stalk (f.left x)) :=
      IsScalarTower.of_algebraMap_eq fun c ↦ (hY c).symm
    have : IsScalarTower Γ(Spec (.of k), ⊤) S₀ (X.left.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_eq fun c ↦ by
        change X.left.presheaf.germ ⊤ x trivial (X.hom.appTop c) =
          f.left.stalkMap x (Y.hom.stalkMap (f.left x)
            ((Spec (.of k)).presheaf.germ ⊤ (Y.hom (f.left x)) trivial c))
        rw [hY, ← Over.w f]
        exact (Scheme.Hom.germ_stalkMap_apply f.left ⊤ x trivial (Y.hom.appTop c)).symm
    exact SmoothTangent.exact_mapBaseChange_map_of_subsingleton (T := S₀)
      (SmoothTangent.stalk_kaehler_transitivity_exact f.left Y.hom x)
  rw [finrank_range_zariskiTangentMap, moduleFiberDim,
    SmoothTangent.finrank_fibre_relativeDifferentials_eq_stalk,
    SmoothTangent.moduleFiberDim_relativeDifferentials_eq_finrank_cotangentSpace X.hom x hx]
  exact CotangentKaehler.finrank_fiber_add_finrank_range Γ(Spec (.of k), ⊤) _ _ hk hex

end ClosedPoint

section Constructible

/-- On a quasi-compact scheme, the fibre dimension of a coherent sheaf is bounded. -/
theorem exists_forall_moduleFiberDim_le {Z : Scheme.{u}} [CompactSpace Z] (G : Z.Modules)
    (hG : IsCoherent G) : ∃ N : ℕ, ∀ z : Z, moduleFiberDim G z ≤ N := by
  choose U hzU hU using exists_nhds_moduleFiberDim_le_of_isCoherent G hG
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z ↦ (U z : Set Z))
    (fun z ↦ (U z).isOpen) (fun z _ ↦ Set.mem_iUnion.2 ⟨z, hzU z⟩)
  refine ⟨t.sup fun z ↦ moduleFiberDim G z, fun z ↦ ?_⟩
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
  exact (hU w z hzw).trans (Finset.le_sup (f := fun z ↦ moduleFiberDim G z) hw)

/-- In a Noetherian topological space, every closed set is constructible. -/
theorem isConstructible_of_isClosed {S : Type*} [TopologicalSpace S]
    [TopologicalSpace.NoetherianSpace S] {s : Set S} (hs : IsClosed s) : IsConstructible s :=
  (IsRetrocompact.isConstructible hs.isOpen_compl
    fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _).of_compl

/-- For coherent sheaves `F` and `G` on a Noetherian scheme and an integer `r`, the set of points
`z` with `dim F ⊗ k(z) ≤ dim G ⊗ k(z) + r` is constructible: it is the finite union over
`i ≤ N` of the locally closed sets `{dim F ⊗ k(z) = i} ∩ {dim G ⊗ k(z) ≥ i - r}`, where `N`
bounds the fibre dimension of `F`. -/
theorem isConstructible_setOf_moduleFiberDim_le {Z : Scheme.{u}} [IsNoetherian Z]
    (F G : Z.Modules) (hF : IsCoherent F) (hG : IsCoherent G) (r : ℕ) :
    IsConstructible {z : Z | moduleFiberDim F z ≤ moduleFiberDim G z + r} := by
  obtain ⟨N, hN⟩ := exists_forall_moduleFiberDim_le F hF
  have hcl : ∀ (H : Z.Modules), IsCoherent H → ∀ n : ℤ,
      IsConstructible {z : Z | n ≤ (moduleFiberDim H z : ℤ)} := fun H hH n ↦
    isConstructible_of_isClosed (isClosed_setOf_le_moduleFiberDim_of_isCoherent H hH n)
  have heq : {z : Z | moduleFiberDim F z ≤ moduleFiberDim G z + r} =
      ⋃ i ∈ Finset.range (N + 1),
        (({z : Z | (i : ℤ) ≤ moduleFiberDim F z} \ {z : Z | (i + 1 : ℤ) ≤ moduleFiberDim F z}) ∩
          {z : Z | (i - r : ℤ) ≤ moduleFiberDim G z}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff,
      Finset.mem_range, exists_prop]
    constructor
    · intro h
      exact ⟨moduleFiberDim F z, Nat.lt_succ_of_le (hN z), ⟨le_rfl, by omega⟩, by omega⟩
    · rintro ⟨i, -, ⟨h₁, h₂⟩, h₃⟩
      omega
  rw [heq]
  exact IsConstructible.biUnion (Finset.finite_toSet _) fun i _ ↦
    ((hcl F hF _).sdiff (hcl F hF _)).inter (hcl G hG _)

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Over (Spec (CommRingCat.of k))}

/-- **Constructibility of the tangent-rank loci.** Let `f : X ⟶ Y` be a morphism of schemes over
an algebraically closed field `k`, with `X` of finite type and `Y` locally of finite type over
`k`. For every `r`, the closed points `x ∈ X` at which the Zariski tangent map
`T_x X → k(x) ⊗ T_{f x} Y` has rank at most `r` are the closed points of a constructible subset
`C` of `X`; one can take for `C` the set where `dim Ω_{X/k} ⊗ k(x) ≤ dim Ω_{X/Y} ⊗ k(x) + r`. -/
theorem exists_isConstructible_tangentRank_le [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) (r : ℕ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    ∃ C : Set X.left, IsConstructible C ∧
      {x : X.left | IsClosed ({x} : Set X.left) ∧
          finrank (ResidueField (X.left.presheaf.stalk x))
            (LinearMap.range (zariskiTangentMap f.left x)) ≤ r} =
        C ∩ {x : X.left | IsClosed ({x} : Set X.left)} := by
  have := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    exact locallyOfFiniteType_of_comp f.left Y.hom
  refine ⟨_, isConstructible_setOf_moduleFiberDim_le (Scheme.relativeDifferentials X.hom)
    (Scheme.relativeDifferentials f.left)
    (Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType X.hom)
    (Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f.left) r, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  refine ⟨fun ⟨hx, h⟩ ↦ ⟨?_, hx⟩, fun ⟨h, hx⟩ ↦ ⟨hx, ?_⟩⟩
  · have := moduleFiberDim_add_finrank_range_zariskiTangentMap f x hx
    omega
  · have := moduleFiberDim_add_finrank_range_zariskiTangentMap f x hx
    omega

end Constructible

section DenseStratum

open TopologicalSpace

/-- An irreducible component `Z` of the closure of a subset `S` of a Noetherian space is closed,
and `S ∩ Z` is dense in `Z`. -/
theorem isClosed_and_closure_inter_eq_of_maximal {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] {S Z : Set α}
    (hZ : Maximal (fun T : Set α ↦ IsIrreducible T ∧ T ⊆ closure S) Z) :
    IsClosed Z ∧ closure (S ∩ Z) = Z := by
  have hcl : IsClosed Z := closure_subset_iff_isClosed.mp
    (hZ.2 ⟨hZ.1.1.closure, closure_minimal hZ.1.2 isClosed_closure⟩ subset_closure)
  refine ⟨hcl, (closure_minimal Set.inter_subset_right hcl).antisymm ?_⟩
  obtain ⟨F, hFirr, hF⟩ :=
    NoetherianSpace.exists_finset_irreducible ⟨closure S, isClosed_closure⟩
  have hF' : closure S = ⋃ s ∈ F, (s : Set α) := by
    simpa [Closeds.coe_finset_sup] using congrArg (fun C : Closeds α ↦ (C : Set α)) hF
  classical
  let G : Finset (Set α) := F.image fun s : Closeds α ↦ closure (S ∩ (s : Set α))
  have hG : Z ⊆ ⋃₀ (G : Set (Set α)) := by
    refine hZ.1.2.trans (closure_minimal ?_ ?_)
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (hF' ▸ subset_closure hx :
        x ∈ ⋃ s ∈ F, (s : Set α))
      exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hs),
        subset_closure ⟨hx, hxs⟩⟩
    · rw [Finset.coe_image, Set.sUnion_image]
      exact isClosed_biUnion_finset fun s _ ↦ isClosed_closure
  obtain ⟨y, hy, hZy⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ.1.1 G
    (fun y hy ↦ by obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hy; exact isClosed_closure) hG
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
  have hsS : (s : Set α) ⊆ closure S := by
    rw [hF']
    exact Set.subset_biUnion_of_mem (u := fun s : Closeds α ↦ (s : Set α)) hs
  have hsZ : (s : Set α) ⊆ Z := hZ.2 ⟨hFirr ⟨s, hs⟩, hsS⟩
    (hZy.trans (closure_minimal Set.inter_subset_right s.isClosed))
  exact hZy.trans (closure_mono (Set.inter_subset_inter_right _ hsZ))

/-- Let `S` be a scheme locally of finite type over an algebraically closed field `k` and `Z` an
irreducible closed subset of `S`. Then there is an open set `V` of `S` meeting `Z` such that the
reduced induced closed subscheme on `Z` is nonsingular at every point lying in `V`: this
subscheme is a variety over `k`, so its regular points contain a nonempty open set. -/
theorem exists_isOpen_isRegularAt_reducedInducedSubscheme {k : Type u} [Field k] [IsAlgClosed k]
    {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (Z : Closeds S)
    (hZ : IsIrreducible (Z : Set S)) :
    ∃ V : Set S, IsOpen V ∧ (V ∩ Z).Nonempty ∧
      ∀ z : reducedInducedSubscheme Z, reducedInducedSubschemeι Z z ∈ V →
        (reducedInducedSubscheme Z).IsRegularAt z := by
  let ι := reducedInducedSubschemeι Z
  have hrange : Set.range ι = Z := range_reducedInducedSubschemeι Z
  have hemb : IsEmbedding ι := ι.isClosedEmbedding.isEmbedding
  have : IrreducibleSpace (reducedInducedSubscheme Z) := by
    have : IrreducibleSpace (Set.range ι) := by
      rw [hrange]
      exact Subtype.irreducibleSpace hZ
    exact (Homeomorph.irreducibleSpace_iff hemb.toHomeomorph).mpr this
  have : IsIntegral (reducedInducedSubscheme Z) := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨U, ⟨u, hu⟩, -, hreg⟩ := exists_nonempty_dense_isRegularAt (k := k) (ι ≫ p)
  obtain ⟨V, hV, hVU⟩ := hemb.isInducing.isOpen_iff.1 U.isOpen
  refine ⟨V, hV, ⟨ι u, ?_, hrange ▸ Set.mem_range_self u⟩, fun z hz ↦ hreg z ?_⟩
  · rw [← Set.mem_preimage, hVU]
    exact hu
  · rw [← SetLike.mem_coe, ← hVU]
    exact hz

/-- A nonempty closed subset `T` of a Noetherian space contains an irreducible closed subset `Z`
and an open set `O` meeting `Z` with `O ∩ T ⊆ Z`. -/
theorem exists_isIrreducible_isOpen_inter_subset {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] {T : Set α} (hT : IsClosed T) (hne : T.Nonempty) :
    ∃ Z O : Set α, IsIrreducible Z ∧ IsClosed Z ∧ Z ⊆ T ∧ IsOpen O ∧ (O ∩ Z).Nonempty ∧
      O ∩ T ⊆ Z := by
  classical
  obtain ⟨F, hFirr, hF⟩ := NoetherianSpace.exists_finset_irreducible ⟨T, hT⟩
  have hF' : T = ⋃ s ∈ F, (s : Set α) := by
    simpa [Closeds.coe_finset_sup] using congrArg (fun C : Closeds α ↦ (C : Set α)) hF
  have hFne : F.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨s, hs, -⟩ := Set.mem_iUnion₂.1 (hF' ▸ hx : x ∈ ⋃ s ∈ F, (s : Set α))
    exact ⟨s, hs⟩
  obtain ⟨Z, hZF, hZmax⟩ := F.exists_maximal hFne
  let T' : Set α := ⋃ s ∈ F.erase Z, (s : Set α)
  have hT' : IsClosed T' := isClosed_biUnion_finset fun s _ ↦ s.isClosed
  refine ⟨Z, T'ᶜ, hFirr ⟨Z, hZF⟩, Z.isClosed, ?_, hT'.isOpen_compl, ?_, ?_⟩
  · rw [hF']
    exact Set.subset_biUnion_of_mem (u := fun s : Closeds α ↦ (s : Set α)) hZF
  · by_contra h
    have hZT' : (Z : Set α) ⊆ ⋃₀ ↑((F.erase Z).image fun s : Closeds α ↦ (s : Set α)) := by
      intro z hz
      by_contra hz'
      refine h ⟨z, fun hzT ↦ hz' ?_, hz⟩
      obtain ⟨s, hs, hzs⟩ := Set.mem_iUnion₂.1 hzT
      exact Set.mem_sUnion.2 ⟨s, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hs), hzs⟩
    obtain ⟨_, hy, hZy⟩ := isIrreducible_iff_sUnion_isClosed.mp (hFirr ⟨Z, hZF⟩) _
      (fun y hy ↦ by obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hy; exact s.isClosed) hZT'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hsZ, hsF⟩ := Finset.mem_erase.1 hs
    exact hsZ (le_antisymm (hZmax hsF hZy) hZy)
  · rintro x ⟨hxT', hxT⟩
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (hF' ▸ hxT : x ∈ ⋃ s ∈ F, (s : Set α))
    by_cases hsZ : s = Z
    · exact hsZ ▸ hxs
    · exact absurd (Set.mem_iUnion₂.2 ⟨s, Finset.mem_erase.2 ⟨hsZ, hs⟩, hxs⟩) hxT'

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Over (Spec (CommRingCat.of k))}

/-- **A stratum of constant tangent rank on an irreducible closed set.** Let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over an algebraically closed field `k`, let `Z` be an
irreducible closed subset of `X`, and let `O` be an open set meeting `Z`. Then there is an open
set `U ⊆ O` meeting `Z` such that the tangent map of `f` has the same rank at every closed point
of `U ∩ Z`, the reduced induced closed subscheme on `Z` is nonsingular at the points of `U ∩ Z`,
and the reduced induced closed subscheme on the closure of `f(Z)` is nonsingular at the points of
`f(U ∩ Z)`. -/
theorem exists_isOpen_subset_tangentRank_eq [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) {Z O : Set X.left} (hZi : IsIrreducible Z)
    (hZc : IsClosed Z) (hO : IsOpen O) (hOZ : (O ∩ Z).Nonempty) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    ∃ U ⊆ O, IsOpen U ∧ (U ∩ Z).Nonempty ∧
      (∃ n : ℕ, ∀ x ∈ U ∩ Z, IsClosed ({x} : Set X.left) →
        finrank (ResidueField (X.left.presheaf.stalk x))
          (LinearMap.range (zariskiTangentMap f.left x)) = n) ∧
      (∀ z : reducedInducedSubscheme ⟨closure Z, isClosed_closure⟩,
        reducedInducedSubschemeι _ z ∈ U → (reducedInducedSubscheme _).IsRegularAt z) ∧
      ∀ w : reducedInducedSubscheme ⟨closure (f.left '' Z), isClosed_closure⟩,
        reducedInducedSubschemeι _ w ∈ f.left '' (U ∩ Z) →
          (reducedInducedSubscheme _).IsRegularAt w := by
  have := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    exact locallyOfFiniteType_of_comp f.left Y.hom
  -- the generic point `η` of `Z`
  let η := hZi.genericPoint
  have hη : closure {η} = Z := by
    have := hZi.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  have hηZ : η ∈ Z := hη ▸ subset_closure rfl
  -- every open set meeting `Z` contains `η`
  have hgen : ∀ V : Set X.left, IsOpen V → (V ∩ Z).Nonempty → η ∈ V := by
    rintro V hV ⟨z, hzV, hzZ⟩
    by_contra h
    have : Z ⊆ Vᶜ := hη ▸ closure_minimal (Set.singleton_subset_iff.2 h) hV.isClosed_compl
    exact this hzZ hzV
  -- the fibre dimensions are at least their generic values on `Z`
  have hge : ∀ G : X.left.Modules, IsCoherent G → ∀ z ∈ Z,
      moduleFiberDim G η ≤ moduleFiberDim G z := by
    intro G hG z hz
    have hc := isClosed_setOf_le_moduleFiberDim_of_isCoherent G hG (moduleFiberDim G η)
    have : Z ⊆ {y : X.left | (moduleFiberDim G η : ℤ) ≤ moduleFiberDim G y} :=
      hη ▸ closure_minimal (Set.singleton_subset_iff.2 (le_refl (moduleFiberDim G η : ℤ))) hc
    exact_mod_cast this hz
  have hk := Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType X.hom
  have hf := Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f.left
  -- and at most their generic values near `η`
  obtain ⟨Ua, hηa, hUa⟩ := exists_nhds_moduleFiberDim_le_of_isCoherent _ hk η
  obtain ⟨Ub, hηb, hUb⟩ := exists_nhds_moduleFiberDim_le_of_isCoherent _ hf η
  -- the regular loci of the reduced induced subschemes on `Z` and on the closure of `f(Z)`
  obtain ⟨VZ, hVZ, hVZne, hregZ⟩ := exists_isOpen_isRegularAt_reducedInducedSubscheme X.hom
    ⟨closure Z, isClosed_closure⟩ hZi.closure
  rw [show ((⟨closure Z, isClosed_closure⟩ : Closeds X.left) : Set X.left) = Z from
    hZc.closure_eq] at hVZne
  obtain ⟨VW, hVW, hVWne, hregW⟩ := exists_isOpen_isRegularAt_reducedInducedSubscheme Y.hom
    ⟨closure (f.left '' Z), isClosed_closure⟩
    (hZi.image f.left f.left.continuous.continuousOn).closure
  have hηW : η ∈ f.left ⁻¹' VW := by
    refine hgen _ (hVW.preimage f.left.continuous) ?_
    obtain ⟨_, ⟨z, hz, rfl⟩, hzV⟩ := (closure_inter_open_nonempty_iff hVW).1
      (Set.inter_comm _ _ ▸ hVWne)
    exact ⟨z, hzV, hz⟩
  let U : Set X.left := O ∩ Ua ∩ Ub ∩ VZ ∩ f.left ⁻¹' VW
  have hU : IsOpen U :=
    (((hO.inter Ua.isOpen).inter Ub.isOpen).inter hVZ).inter (hVW.preimage f.left.continuous)
  have hηU : η ∈ U ∩ Z :=
    ⟨⟨⟨⟨⟨hgen O hO hOZ, hηa⟩, hηb⟩, hgen VZ hVZ hVZne⟩, hηW⟩, hηZ⟩
  refine ⟨U, fun x hx ↦ hx.1.1.1.1, hU, ⟨η, hηU⟩,
    ⟨moduleFiberDim (Scheme.relativeDifferentials X.hom) η -
      moduleFiberDim (Scheme.relativeDifferentials f.left) η, ?_⟩,
    fun z hz ↦ hregZ z hz.1.2, ?_⟩
  · rintro x ⟨⟨⟨⟨⟨-, hxa⟩, hxb⟩, -⟩, -⟩, hxZ⟩ hx
    have h₁ := hUa x hxa
    have h₂ := hUb x hxb
    have h₃ := hge _ hk x hxZ
    have h₄ := hge _ hf x hxZ
    have := moduleFiberDim_add_finrank_range_zariskiTangentMap f x hx
    omega
  · rintro w ⟨x, hx, hxw⟩
    exact hregW w (hxw ▸ hx.1.2)

/-- **A dense stratum of constant tangent rank.** Let `f : X ⟶ Y` be a morphism of schemes over an
algebraically closed field `k`, with `X` of finite type and `Y` locally of finite type over `k`,
and let `Z` be an irreducible component of the closure of the set `X_r` of closed points at which
the tangent map of `f` has rank at most `r`. Then there is an open set `U` of `X` meeting `Z` (so
that `U ∩ Z` is a dense irreducible open subset of `Z`) such that the tangent map has the same
rank `n ≤ r` at every closed point of `U ∩ Z`, the closed points of `U ∩ Z` are dense in `Z`, and
their images are closed points of `Y`, dense in the closure of `f(Z)`. Moreover the reduced
induced closed subschemes on `Z` and on the closure of `f(Z)` are nonsingular at the points of
`U ∩ Z` and of `f(U ∩ Z)` respectively. -/
theorem exists_isOpen_tangentRank_eq_of_maximal [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) (r : ℕ) {Z : Set X.left}
    (hZ : haveI := LocallyOfFiniteType.isLocallyNoetherian Y.hom
      Maximal (fun T : Set X.left ↦ IsIrreducible T ∧ T ⊆ closure
        {x : X.left | IsClosed ({x} : Set X.left) ∧
          finrank (ResidueField (X.left.presheaf.stalk x))
            (LinearMap.range (zariskiTangentMap f.left x)) ≤ r}) Z) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    ∃ U : Set X.left, IsOpen U ∧ (U ∩ Z).Nonempty ∧
      (∃ n ≤ r, ∀ x ∈ U ∩ Z, IsClosed ({x} : Set X.left) →
        finrank (ResidueField (X.left.presheaf.stalk x))
          (LinearMap.range (zariskiTangentMap f.left x)) = n) ∧
      closure (U ∩ Z ∩ {x : X.left | IsClosed ({x} : Set X.left)}) = Z ∧
      f.left '' (U ∩ Z ∩ {x : X.left | IsClosed ({x} : Set X.left)}) ⊆
        {y : Y.left | IsClosed ({y} : Set Y.left)} ∧
      closure (f.left '' (U ∩ Z ∩ {x : X.left | IsClosed ({x} : Set X.left)})) =
        closure (f.left '' Z) ∧
      (∀ z : reducedInducedSubscheme ⟨closure Z, isClosed_closure⟩,
        reducedInducedSubschemeι _ z ∈ U → (reducedInducedSubscheme _).IsRegularAt z) ∧
      ∀ w : reducedInducedSubscheme ⟨closure (f.left '' Z), isClosed_closure⟩,
        reducedInducedSubschemeι _ w ∈ f.left '' (U ∩ Z) →
          (reducedInducedSubscheme _).IsRegularAt w := by
  have := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    exact locallyOfFiniteType_of_comp f.left Y.hom
  obtain ⟨hZc, hSZ⟩ := isClosed_and_closure_inter_eq_of_maximal hZ
  obtain ⟨z₀, hz₀⟩ := hZ.1.1.nonempty
  obtain ⟨U, -, hU, hUZ, ⟨n, hn⟩, hregZ, hregW⟩ := exists_isOpen_subset_tangentRank_eq f hZ.1.1 hZc
    isOpen_univ ⟨z₀, trivial, hz₀⟩
  -- `U ∩ Z` is dense in `Z`, and so are its closed points
  have hdense : closure (U ∩ Z ∩ {x : X.left | IsClosed ({x} : Set X.left)}) = Z := by
    rw [show U ∩ Z ∩ {x : X.left | IsClosed ({x} : Set X.left)} =
        U ∩ Z ∩ closedPoints X.left from rfl,
      JacobsonSpace.closure_inter_closedPoints_eq_closure
        (hU.isLocallyClosed.inter hZc.isLocallyClosed)]
    refine (closure_minimal Set.inter_subset_right hZc).antisymm ?_
    rw [Set.inter_comm]
    exact subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.1.2 hU
      (Set.inter_comm U Z ▸ hUZ)
  -- `U ∩ Z` meets `X_r`, which bounds the rank
  obtain ⟨u, huU, huZ⟩ := hUZ
  obtain ⟨x, hxU, hxS, hxZ⟩ := mem_closure_iff.1 (hSZ.symm ▸ huZ : u ∈ closure _) U hU huU
  refine ⟨U, hU, ⟨u, huU, huZ⟩, ⟨n, (hn x ⟨hxU, hxZ⟩ hxS.1) ▸ hxS.2, hn⟩, hdense, ?_, ?_,
    hregZ, hregW⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact f.left.closePoints_subset_preimage_closedPoints hx.2
  · refine (closure_mono (Set.image_mono fun x hx ↦ hx.1.2)).antisymm
      (closure_minimal ?_ isClosed_closure)
    conv_lhs => rw [← hdense]
    exact image_closure_subset_closure_image f.left.continuous

/-- **A finite stratification by tangent rank.** Let `f : X ⟶ Y` be a morphism of schemes over an
algebraically closed field `k`, with `X` of finite type and `Y` locally of finite type over `k`.
Then `X` is the disjoint union of finitely many locally closed strata `U ∩ Z`, indexed by pairs
`(Z, U)` with `Z` irreducible and closed, `U` open and `U ∩ Z` nonempty (hence dense in `Z`),
such that on each stratum the tangent map of `f` has constant rank at the closed points, the
reduced induced closed subscheme on `Z` is nonsingular at the points of the stratum, and the
reduced induced closed subscheme on the closure of `f(Z)` is nonsingular at the points of the
image of the stratum. -/
theorem exists_finite_tangentRank_stratification [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    ∃ S : Set (Set X.left × Set X.left), S.Finite ∧
      S.PairwiseDisjoint (fun p ↦ p.2 ∩ p.1) ∧ (⋃ p ∈ S, p.2 ∩ p.1) = Set.univ ∧
      ∀ p ∈ S, IsIrreducible p.1 ∧ IsClosed p.1 ∧ IsOpen p.2 ∧ (p.2 ∩ p.1).Nonempty ∧
        (∃ n : ℕ, ∀ x ∈ p.2 ∩ p.1, IsClosed ({x} : Set X.left) →
          finrank (ResidueField (X.left.presheaf.stalk x))
            (LinearMap.range (zariskiTangentMap f.left x)) = n) ∧
        (∀ z : reducedInducedSubscheme ⟨closure p.1, isClosed_closure⟩,
          reducedInducedSubschemeι _ z ∈ p.2 → (reducedInducedSubscheme _).IsRegularAt z) ∧
        ∀ w : reducedInducedSubscheme ⟨closure (f.left '' p.1), isClosed_closure⟩,
          reducedInducedSubschemeι _ w ∈ f.left '' (p.2 ∩ p.1) →
            (reducedInducedSubscheme _).IsRegularAt w := by
  have := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  -- Noetherian induction over the closed subsets `T` of `X`
  suffices H : ∀ T : Closeds X.left, ∃ S : Set (Set X.left × Set X.left), S.Finite ∧
      S.PairwiseDisjoint (fun p ↦ p.2 ∩ p.1) ∧ (⋃ p ∈ S, p.2 ∩ p.1) = T ∧
      ∀ p ∈ S, IsIrreducible p.1 ∧ IsClosed p.1 ∧ IsOpen p.2 ∧ (p.2 ∩ p.1).Nonempty ∧
        (∃ n : ℕ, ∀ x ∈ p.2 ∩ p.1, IsClosed ({x} : Set X.left) →
          finrank (ResidueField (X.left.presheaf.stalk x))
            (LinearMap.range (zariskiTangentMap f.left x)) = n) ∧
        (∀ z : reducedInducedSubscheme ⟨closure p.1, isClosed_closure⟩,
          reducedInducedSubschemeι _ z ∈ p.2 → (reducedInducedSubscheme _).IsRegularAt z) ∧
        ∀ w : reducedInducedSubscheme ⟨closure (f.left '' p.1), isClosed_closure⟩,
          reducedInducedSubschemeι _ w ∈ f.left '' (p.2 ∩ p.1) →
            (reducedInducedSubscheme _).IsRegularAt w from H ⊤
  intro T
  induction T using WellFoundedLT.induction with
  | _ T ih =>
  by_cases hne : (T : Set X.left).Nonempty
  · obtain ⟨Z, O, hZi, hZc, hZT, hO, hOZ, hOT⟩ :=
      exists_isIrreducible_isOpen_inter_subset T.isClosed hne
    obtain ⟨U, hUO, hU, hUZ, hn, hregZ, hregW⟩ :=
      exists_isOpen_subset_tangentRank_eq f hZi hZc hO hOZ
    -- the stratum `U ∩ Z` is `U ∩ T`, open in `T`
    have hUT : U ∩ Z = U ∩ T := Set.Subset.antisymm (Set.inter_subset_inter_right _ hZT)
      fun x hx ↦ ⟨hx.1, hOT ⟨hUO hx.1, hx.2⟩⟩
    let T₁ : Closeds X.left := ⟨T ∩ Uᶜ, T.isClosed.inter hU.isClosed_compl⟩
    have hlt : T₁ < T := by
      refine lt_of_le_of_ne (fun x hx ↦ hx.1) fun h ↦ ?_
      obtain ⟨x, hxU, hxZ⟩ := hUZ
      have : x ∈ (T₁ : Set X.left) := h ▸ hZT hxZ
      exact this.2 hxU
    obtain ⟨S, hSf, hSd, hSU, hSg⟩ := ih T₁ hlt
    have hsub : ∀ p ∈ S, p.2 ∩ p.1 ⊆ (T : Set X.left) ∩ Uᶜ := fun p hp x hx ↦
      (hSU ▸ Set.mem_biUnion hp hx : x ∈ (T₁ : Set X.left))
    refine ⟨insert (Z, U) S, hSf.insert _, hSd.insert fun p hp _ ↦ ?_, ?_, ?_⟩
    · exact Set.disjoint_left.2 fun x hx hx' ↦ (hsub p hp hx').2 hx.1
    · rw [Set.biUnion_insert, hSU]
      change U ∩ Z ∪ T ∩ Uᶜ = T
      rw [hUT]
      ext x
      by_cases hx : x ∈ U <;> simp [hx]
    · rintro p (rfl | hp)
      · exact ⟨hZi, hZc, hU, hUZ, hn, hregZ, hregW⟩
      · exact hSg p hp
  · refine ⟨∅, Set.finite_empty, Set.pairwiseDisjoint_empty, ?_, by simp⟩
    rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

end DenseStratum

end TangentRank

end

end Hartshorne
