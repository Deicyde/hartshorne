/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.SmoothTangentCriterion
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

end TangentRank

end

end Hartshorne
