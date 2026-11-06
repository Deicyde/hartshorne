/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VarietySchemeOverK
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Classical points are the closed points

Hartshorne, *Algebraic Geometry*, II.2, the closed-point clause of
Proposition 2.6 and Exercise 2.15(a) (pp. 78–81).

For a variety `V` with an affine-open basis over an algebraically closed field
`k`, the map `α_V : V → t(V)`, `x ↦ closure {x}`, is a homeomorphism onto the
subspace of closed points of the associated scheme `t(V)`; and a point of
`t(V)` is closed exactly when its residue field is `k`, that is, when the
composite `k → 𝒪_{t(V),z} → κ(z)` of the constant regular functions with the
residue map is bijective.

## Proof

* In the generic completion of any space, `Z'` lies in the closure of `{Z}`
  exactly when `Z' ⊆ Z`. For a `T₁` space this makes the closed points exactly
  the points `closure {x} = {x}`, and `α` is an embedding because the opens of
  `t(X)` are exactly the sets `{Z | Z ∩ U ≠ ∅}`, whose preimages are the opens
  `U`.
* A variety with an affine-open basis is `T₁`: on an affine open neighbourhood
  regular coordinate functions separate points, and their non-vanishing loci
  are open.
* At `z = α(x)`, evaluation at `x` is a ring map from the stalk to `k` sending
  each constant to itself; so every germ differs from a constant by a non-unit,
  and the residue map from `k` is surjective.
* If `z = Z` is not of the form `α(x)`, then `Z` meets an affine open `U` in
  two distinct points, a coordinate function `f` on `U` separates them, and for
  every constant `c` the germ of `f - c` at `z` is a unit, since `f - c` is
  invertible on the open set where it does not vanish, which meets `Z`. Hence
  the residue class of `f` is not a constant.

## Main definitions and results

* `Hartshorne.varietyAssociatedSchemeAlpha`: the map `α_V : V → t(V)`.
* `Hartshorne.varietyAssociatedScheme_isEmbedding_alpha_and_range`:
  `α_V` is an embedding with image the closed points.
* `Hartshorne.varietyClosedPointsHomeomorph`: the resulting homeomorphism from
  `V` onto the subspace of closed points.
* `Hartshorne.varietyAssociatedSchemeResidueConstants`: the composite
  `k → Γ(t(V), 𝒪) → 𝒪_{t(V),z} → κ(z)`.
* `Hartshorne.varietyAssociatedScheme_isClosed_singleton_iff`: a point of `t(V)`
  is closed iff that composite is bijective.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry Limits

namespace Hartshorne

universe u

/-! ### Closed points of the generic completion -/

section GenericCompletion

variable {X : Type u} [TopologicalSpace X]

/-- In the generic completion, `Z'` lies in the closure of `{Z}` exactly when
`Z' ⊆ Z`. -/
theorem genericCompletion_mem_closure_singleton_iff {Z Z' : IrreducibleCloseds X} :
    Z' ∈ @closure _ (genericCompletionTopology (TopCat.of X)) {Z} ↔
      (Z' : Set X) ⊆ Z := by
  let _ : TopologicalSpace (IrreducibleCloseds X) := genericCompletionTopology (TopCat.of X)
  constructor
  · intro h
    have hc : IsClosed {W : IrreducibleCloseds X | (W : Set X) ⊆ Z} :=
      (genericCompletion_isClosed_iff (TopCat.of X) _).2 ⟨Z, Z.isClosed, rfl⟩
    refine closure_minimal ?_ hc h
    intro W hW
    rw [Set.mem_singleton_iff.1 hW]
    exact subset_refl (Z : Set X)
  · intro h
    obtain ⟨C, -, hC⟩ := (genericCompletion_isClosed_iff (TopCat.of X) _).1
      (isClosed_closure (s := ({Z} : Set (IrreducibleCloseds X))))
    have hZ : Z ∈ closure ({Z} : Set (IrreducibleCloseds X)) := subset_closure rfl
    rw [hC] at hZ ⊢
    exact fun _ hx => hZ (h hx)

theorem genericCompletionAlphaPoint_coe [T1Space X] (x : X) :
    (genericCompletionAlphaPoint (TopCat.of X) x : Set X) = {x} :=
  closure_singleton

/-- For a `T₁` space, the closed points of the generic completion are exactly
the points `closure {x}`. -/
theorem genericCompletion_isClosed_singleton_iff [T1Space X] (Z : IrreducibleCloseds X) :
    @IsClosed _ (genericCompletionTopology (TopCat.of X)) {Z} ↔
      ∃ x : X, genericCompletionAlphaPoint (TopCat.of X) x = Z := by
  let _ : TopologicalSpace (IrreducibleCloseds X) := genericCompletionTopology (TopCat.of X)
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
    refine ⟨x, ?_⟩
    have hmem : genericCompletionAlphaPoint (TopCat.of X) x ∈
        closure ({Z} : Set (IrreducibleCloseds X)) := by
      rw [genericCompletion_mem_closure_singleton_iff, genericCompletionAlphaPoint_coe]
      exact Set.singleton_subset_iff.2 hx
    rw [h.closure_eq] at hmem
    exact hmem
  · rintro ⟨x, rfl⟩
    refine closure_subset_iff_isClosed.1 fun Z' hZ' => ?_
    rw [genericCompletion_mem_closure_singleton_iff, genericCompletionAlphaPoint_coe] at hZ'
    refine Set.mem_singleton_iff.2 (IrreducibleCloseds.ext ?_)
    rw [genericCompletionAlphaPoint_coe]
    exact (Set.subset_singleton_iff_eq.1 hZ').resolve_left Z'.isIrreducible.nonempty.ne_empty

/-- For a `T₁` space `X`, the map `α : X → t(X)` is an embedding. -/
theorem genericCompletion_isEmbedding_alphaPoint [T1Space X] :
    @IsEmbedding _ _ _ (genericCompletionTopology (TopCat.of X))
      (genericCompletionAlphaPoint (TopCat.of X)) := by
  let _ : TopologicalSpace (IrreducibleCloseds X) := genericCompletionTopology (TopCat.of X)
  have hcont : Continuous (genericCompletionAlphaPoint (TopCat.of X)) :=
    (genericCompletionAlpha (TopCat.of X)).hom.continuous
  refine ⟨⟨le_antisymm hcont.le_induced ?_⟩, fun x y h => ?_⟩
  · rw [TopologicalSpace.le_def]
    intro s hs
    rw [isOpen_induced_iff]
    exact ⟨genericCompletionOpen (TopCat.of X) ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩,
      congrArg SetLike.coe
        ((genericCompletionOpensOrderIso (TopCat.of X)).symm_apply_apply ⟨s, hs⟩)⟩
  · have := congrArg (fun Z : IrreducibleCloseds X => (Z : Set X)) h
    change (genericCompletionAlphaPoint (TopCat.of X) x : Set X) =
      genericCompletionAlphaPoint (TopCat.of X) y at this
    rw [genericCompletionAlphaPoint_coe, genericCompletionAlphaPoint_coe] at this
    exact Set.singleton_injective this

end GenericCompletion

/-! ### Varieties with an affine-open basis are `T₁` -/

variable {k : Type u} [Field k]

/-- Every point of a variety with an affine-open basis has an open
neighbourhood on which regular functions separate points. -/
theorem Variety.exists_open_regular_separating (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) (y : V.carrier) :
    ∃ U : Opens V.carrier, y ∈ U ∧
      ∀ p q : U, p ≠ q → ∃ f ∈ V.regular U, f p ≠ f q := by
  obtain ⟨U, hU, hyU, -, σ, hσ, Y, hY, φ, ψ, hψφ, -⟩ := hV ⊤ y trivial
  refine ⟨U, hyU, fun p q hpq => ?_⟩
  have hinj : φ p ≠ φ q := fun h => hpq (by
    have h1 : ψ (φ p) = p :=
      congrArg (fun g : VarietyHom (V.restrict U hU) (V.restrict U hU) =>
        g (p : (V.restrict U hU).carrier)) hψφ
    have h2 : ψ (φ q) = q :=
      congrArg (fun g : VarietyHom (V.restrict U hU) (V.restrict U hU) =>
        g (q : (V.restrict U hU).carrier)) hψφ
    rw [← h1, ← h2, h])
  obtain ⟨i, hi⟩ := Function.ne_iff.1 fun h => hinj (Subtype.ext h)
  have hcoord :=
    (exists_varietyHom_iff_coords_regular hY.isQuasiAffineVariety φ.toFun).1 ⟨φ, rfl⟩ i
  exact ⟨fun r : U => (φ r).1 i,
    V.regular_restrict (U := pushOpens U ⊤) (fun r hr => ⟨hr, fun _ => trivial⟩) hcoord, hi⟩

/-- The locus where a regular function differs from a constant is open. -/
theorem Variety.isOpen_image_regular_ne (V : Variety.{u, u} k) {U : Opens V.carrier}
    {f : U → k} (hf : f ∈ V.regular U) (c : k) :
    IsOpen (Subtype.val '' {p : U | f p ≠ c}) := by
  have hg : f - algebraMap k (U → k) c ∈ V.regular U :=
    sub_mem hf (Subalgebra.algebraMap_mem _ c)
  refine U.isOpen.isOpenMap_subtype_val _ ?_
  have hset : {p : U | f p ≠ c} = {p : U | (f - algebraMap k (U → k) c) p = 0}ᶜ := by
    ext p
    change f p ≠ c ↔ ¬ (f p - c = 0)
    rw [sub_eq_zero]
  rw [hset]
  exact (V.isClosed_zeroLocus hg).isOpen_compl

/-- A variety with an affine-open basis is a `T₁` space. -/
theorem Variety.t1Space_of_hasAffineOpenBasis (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) : T1Space V.carrier := by
  refine t1Space_iff_exists_open.2 fun x y hxy => ?_
  obtain ⟨U, hxU, hsep⟩ := V.exists_open_regular_separating hV x
  by_cases hyU : y ∈ U
  · obtain ⟨f, hf, hne⟩ := hsep ⟨x, hxU⟩ ⟨y, hyU⟩ fun h => hxy (congrArg Subtype.val h)
    refine ⟨_, V.isOpen_image_regular_ne hf (f ⟨y, hyU⟩), ⟨⟨x, hxU⟩, hne, rfl⟩, ?_⟩
    rintro ⟨p, hp, hpy⟩
    exact hp (congrArg f (Subtype.ext hpy))
  · exact ⟨U, U.isOpen, hxU, hyU⟩

/-- A regular function without zeros is a unit. -/
theorem Variety.isUnit_of_forall_ne_zero (V : Variety.{u, u} k) {U : Opens V.carrier}
    (g : V.regular U) (hg : ∀ p, g.1 p ≠ 0) : IsUnit g :=
  isUnit_iff_exists_inv.2 ⟨⟨fun p => 1 / g.1 p, V.regular_div (one_mem _) g.2 hg⟩,
    Subtype.ext (funext fun p => mul_one_div_cancel (hg p))⟩

/-! ### The closed points of the associated scheme -/

section AlgClosed

variable [IsAlgClosed k]

/-- **Hartshorne II.2, Proposition 2.6.** The map `α_V : V → t(V)`,
`x ↦ closure {x}`, into the associated scheme. -/
def varietyAssociatedSchemeAlpha (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    V.carrier → varietyAssociatedScheme V hV :=
  genericCompletionAlphaPoint (TopCat.of V.carrier)

/-- **Hartshorne II.2, Proposition 2.6 (p. 78).** For a variety `V` over an
algebraically closed field (with an affine-open basis), `α_V : V → t(V)` is a
homeomorphism onto the subspace of closed points of the associated scheme: it
is an embedding whose image is the set of closed points. -/
theorem varietyAssociatedScheme_isEmbedding_alpha_and_range (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) :
    IsEmbedding (varietyAssociatedSchemeAlpha V hV) ∧
      Set.range (varietyAssociatedSchemeAlpha V hV) =
        {z : varietyAssociatedScheme V hV | IsClosed ({z} : Set (varietyAssociatedScheme V hV))} := by
  have := V.t1Space_of_hasAffineOpenBasis hV
  refine ⟨genericCompletion_isEmbedding_alphaPoint, ?_⟩
  ext z
  exact (genericCompletion_isClosed_singleton_iff (X := V.carrier) z).symm

/-- **Hartshorne II.2, Proposition 2.6 (p. 78).** The homeomorphism from `V`
onto the subspace of closed points of its associated scheme induced by
`α_V`. -/
def varietyClosedPointsHomeomorph (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    V.carrier ≃ₜ
      {z : varietyAssociatedScheme V hV // IsClosed ({z} : Set (varietyAssociatedScheme V hV))} :=
  ((varietyAssociatedScheme_isEmbedding_alpha_and_range V hV).1.toHomeomorph).trans
    (Homeomorph.setCongr (varietyAssociatedScheme_isEmbedding_alpha_and_range V hV).2)

@[simp]
theorem varietyClosedPointsHomeomorph_apply (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) (x : V.carrier) :
    (varietyClosedPointsHomeomorph V hV x : varietyAssociatedScheme V hV) =
      varietyAssociatedSchemeAlpha V hV x :=
  rfl

/-- The composite `k → Γ(t(V), 𝒪) → 𝒪_{t(V),z} → κ(z)` of the constant regular
functions, the germ at `z` and the residue map. -/
def varietyAssociatedSchemeResidueConstants (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis)
    (z : varietyAssociatedScheme V hV) : k →+* (varietyAssociatedScheme V hV).residueField z :=
  (varietyAssociatedSchemeConstants V hV ≫
    (varietyAssociatedScheme V hV).presheaf.germ ⊤ z trivial ≫
      (varietyAssociatedScheme V hV).residue z).hom

/-- Evaluation at `x` of germs at `α_V(x)`. -/
def varietyAssociatedSchemeStalkEval (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis)
    (x : V.carrier) :
    (varietyAssociatedScheme V hV).presheaf.stalk (varietyAssociatedSchemeAlpha V hV x) ⟶
      CommRingCat.of k :=
  colimit.desc _
    { pt := CommRingCat.of k
      ι :=
        { app := fun W => CommRingCat.ofHom
            ((Pi.evalRingHom (fun _ => k) ⟨x, W.unop.2⟩).comp (V.regular _).val.toRingHom)
          naturality := fun _ _ _ => rfl } }

theorem varietyAssociatedSchemeStalkEval_germ (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) (x : V.carrier)
    (W : Opens (varietyAssociatedScheme V hV)) (hW : varietyAssociatedSchemeAlpha V hV x ∈ W)
    (f : V.regular ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm W)) :
    varietyAssociatedSchemeStalkEval V hV x
        ((varietyAssociatedScheme V hV).presheaf.germ W _ hW f) = f.1 ⟨x, hW⟩ := by
  change ((varietyAssociatedScheme V hV).presheaf.germ W _ hW ≫
    varietyAssociatedSchemeStalkEval V hV x) f = _
  erw [colimit.ι_desc]
  rfl

/-- **Hartshorne II.2, Proposition 2.6 and Exercise 2.15(a) (pp. 78–81).** A
point `z` of the associated scheme `t(V)` is closed if and only if its residue
field is `k`, that is, the composite `k → 𝒪_{t(V),z} → κ(z)` is bijective. -/
theorem varietyAssociatedScheme_isClosed_singleton_iff (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) (z : varietyAssociatedScheme V hV) :
    IsClosed ({z} : Set (varietyAssociatedScheme V hV)) ↔
      Function.Bijective (varietyAssociatedSchemeResidueConstants V hV z) := by
  have := V.t1Space_of_hasAffineOpenBasis hV
  refine (genericCompletion_isClosed_singleton_iff (X := V.carrier) z).trans ?_
  change (∃ x, varietyAssociatedSchemeAlpha V hV x = z) ↔ _
  let X := varietyAssociatedScheme V hV
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨RingHom.injective _, fun r => ?_⟩
    obtain ⟨s, rfl⟩ := X.residue_surjective _ r
    set ev := varietyAssociatedSchemeStalkEval V hV x
    refine ⟨ev s, ?_⟩
    set t := X.presheaf.germ ⊤ (varietyAssociatedSchemeAlpha V hV x) trivial
      (varietyAssociatedSchemeConstants V hV (ev s))
    have hevt : ev t = ev s := varietyAssociatedSchemeStalkEval_germ V hV x ⊤ trivial _
    have hmem : s - t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk _) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map ev.hom
      rw [map_sub, hevt, sub_self] at this
      exact not_isUnit_zero this
    change IsLocalRing.residue _ t = IsLocalRing.residue _ s
    rw [eq_comm, ← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hmem
  · intro hbij
    by_contra hz
    push Not at hz
    let Z : IrreducibleCloseds V.carrier := z
    obtain ⟨y, hyZ⟩ := Z.isIrreducible.nonempty
    obtain ⟨U, hyU, hsep⟩ := V.exists_open_regular_separating hV y
    -- A second point of `Z ∩ U`.
    obtain ⟨y', hy'Z, hy'U, hy'y⟩ : ∃ y' ∈ (Z : Set V.carrier), y' ∈ U ∧ y' ≠ y := by
      have hne : ((Z : Set V.carrier) ∩ ({y}ᶜ : Set V.carrier)).Nonempty := by
        by_contra hempty
        apply hz y
        change genericCompletionAlphaPoint (TopCat.of V.carrier) y = Z
        refine IrreducibleCloseds.ext ?_
        rw [genericCompletionAlphaPoint_coe]
        refine (Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 hyZ)).symm
        intro w hw
        by_contra hwy
        exact hempty ⟨w, hw, hwy⟩
      obtain ⟨w, hwZ, hwU, hwy⟩ :=
        Z.isIrreducible.2 U {y}ᶜ U.isOpen isOpen_compl_singleton ⟨y, hyZ, hyU⟩ hne
      exact ⟨w, hwZ, hwU, hwy⟩
    obtain ⟨f, hf, hfne⟩ := hsep ⟨y, hyU⟩ ⟨y', hy'U⟩ fun h => hy'y (congrArg Subtype.val h).symm
    -- The germ of `f` at `z`.
    let W : Opens X := genericCompletionOpensOrderIso (TopCat.of V.carrier) U
    have hUW : (genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm W = U :=
      (genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm_apply_apply U
    let f' : V.regular ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm W) :=
      ⟨_, V.regular_restrict hUW.le hf⟩
    have hzW : z ∈ W := ⟨y, hyZ, hyU⟩
    obtain ⟨c, hc⟩ := hbij.2 (X.residue z (X.presheaf.germ W z hzW f'))
    -- A point of `Z ∩ U` where `f ≠ c`.
    obtain ⟨w, hwZ, hwU, hfw⟩ : ∃ w ∈ (Z : Set V.carrier), ∃ hwU : w ∈ U, f ⟨w, hwU⟩ ≠ c := by
      by_cases hyc : f ⟨y, hyU⟩ = c
      · exact ⟨y', hy'Z, hy'U, fun h => hfne (hyc.trans h.symm)⟩
      · exact ⟨y, hyZ, hyU, hyc⟩
    let U' : Opens V.carrier := ⟨_, V.isOpen_image_regular_ne hf c⟩
    let W' : Opens X := W ⊓ genericCompletionOpensOrderIso (TopCat.of V.carrier) U'
    have hzW' : z ∈ W' := ⟨hzW, w, hwZ, ⟨w, hwU⟩, hfw, rfl⟩
    let g : V.regular ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm W') :=
      X.presheaf.map (homOfLE inf_le_left).op f' -
        X.presheaf.map (homOfLE le_top).op (varietyAssociatedSchemeConstants V hV c)
    have hg : IsUnit g := by
      refine V.isUnit_of_forall_ne_zero g fun p => ?_
      have hpU' : p.1 ∈ U' := by
        have := SetLike.ext_iff.1
          ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm_apply_apply U') p.1
        exact this.1 p.2.2
      obtain ⟨q, hq, hqp⟩ := hpU'
      change f ⟨p.1, _⟩ - c ≠ 0
      rw [sub_ne_zero]
      exact fun h => hq ((congrArg f (Subtype.ext hqp)).trans h)
    have hgerm : X.presheaf.germ W' z hzW' g =
        X.presheaf.germ W z hzW f' -
          X.presheaf.germ ⊤ z trivial (varietyAssociatedSchemeConstants V hV c) := by
      change X.presheaf.germ W' z hzW' (X.presheaf.map (homOfLE inf_le_left).op f' -
        X.presheaf.map (homOfLE le_top).op (varietyAssociatedSchemeConstants V hV c)) = _
      rw [map_sub]
      erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    have hunit := hg.map (X.presheaf.germ W' z hzW').hom
    have hmem : X.presheaf.germ W z hzW f' -
        X.presheaf.germ ⊤ z trivial (varietyAssociatedSchemeConstants V hV c) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact hc.symm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← hgerm] at hmem
    exact hmem hunit

end AlgClosed

end Hartshorne
