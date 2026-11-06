/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.NormalFundamentalLocus
import Hartshorne.Scheme.Regular
import Hartshorne.Scheme.SerreNormalityCriterion
import Hartshorne.Scheme.RegularLocalCohenMacaulay
import Mathlib.AlgebraicGeometry.Birational.Composition
import Mathlib.Topology.NoetherianSpace

/-!
# Curves contracted by a birational morphism of surfaces

Hartshorne, *Algebraic Geometry*, V.5, first part of Corollary 5.4, pp. 411--412.

For a birational morphism `f : X' ⟶ X` of nonsingular projective surfaces over a field `k`,
only finitely many irreducible curves of `X'` are mapped to points; `n(f)` is their number.

Varieties are encoded as in Lemma V.5.1
(`Hartshorne.SchemeRationalMap.normal_projective_surface_fundamentalLocus_finite`): integral
schemes over `Spec k` whose structure morphism is `Hartshorne.Projective`, and a surface has
topological Krull dimension two. Nonsingularity is `Scheme.IsRegular`. A morphism
`f : X' ⟶ X` is birational when its rational map is represented by a partial isomorphism over
`Spec k`; this already forces `f` to be a `k`-morphism, so no separate hypothesis is recorded.
An irreducible curve of `X'` is an irreducible closed subset of topological Krull dimension
one, and it is contracted when its image under `f` is a single point. The field is arbitrary.

## Proof

Let `T : X ⤏ X'` be the inverse rational map. Since `T ∘ f` is the identity rational map,
for every `p ∈ Dom(T)` the composite `f⁻¹(Dom T) ⟶ Dom T ⟶ X'` agrees with the inclusion on
a dense open set, hence everywhere because `X'` is reduced and separated; so the fibre of `f`
over `p` has at most one point and contains no curve. Thus every contracted curve lies over a
point of the fundamental locus `F` of `T`. A regular scheme is normal (Serre's criterion,
using that regular local rings are Cohen--Macaulay), so by Lemma V.5.1 `F` is a finite set of
closed points. The closed set `f⁻¹(F)` has finitely many irreducible components, and each
contracted curve `C` lies in one of them, say `Z`. The image of `Z` is an irreducible subset of
`F`, hence a point. If `C ≠ Z`, then `Z` has height at least two among the irreducible closed
subsets of `X'`, hence (as `dim X' = 2`) coheight zero, so `Z = X'` and `f` is constant; this
contradicts the dominance of `f` since `X` has more than one point. So every contracted curve
is an irreducible component of `f⁻¹(F)`, and there are finitely many.

The nonsingularity of `X'` is not used: the argument needs only that `X` is normal and that
`X'` is an integral projective surface. The general form with `X` normal is stated first.

## Main results

* `Hartshorne.contractedCurves`, `Hartshorne.numContractedCurves`: the contracted irreducible
  curves of a morphism and their number `n(f)`.
* `Hartshorne.contractedCurves_finite_of_isNormal`: the general form, with `X` normal.
* `Hartshorne.contractedCurves_finite`: Corollary V.5.4, first part.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace Hartshorne

universe u

/-! ### Topological preliminaries -/

/-- The topological dimension of an irreducible closed subset is at most its height
in the poset of irreducible closed subsets. -/
theorem topologicalKrullDim_le_height {X : Type*} [TopologicalSpace X]
    (C : IrreducibleCloseds X) : topologicalKrullDim (C : Set X) ≤ Order.height C := by
  rw [Order.height_eq_krullDim_Iic]
  refine Order.krullDim_le_of_strictMono
    (fun Z => (⟨IrreducibleCloseds.map Subtype.val continuous_subtype_val Z,
      closure_minimal (Subtype.coe_image_subset _ _) C.isClosed⟩ : Set.Iic C)) ?_
  intro a b hab
  exact (IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal hab :)

/-- **Topological core.** Let `φ : X' → X` be continuous with dense range, where `X'` is an
irreducible Noetherian space of dimension two and `X` has at least two points. Suppose that
there is a finite set `F` of closed points of `X` such that every fibre over a point outside
`F` has at most one point. Then only finitely many irreducible closed subsets of `X'` of
dimension one are mapped to points. -/
theorem finite_contracted_of_subsingleton_fibres {X' X : Type*} [TopologicalSpace X']
    [TopologicalSpace X] [IrreducibleSpace X'] [NoetherianSpace X'] [Nontrivial X]
    (hdim : topologicalKrullDim X' = 2) (φ : X' → X) (hφ : Continuous φ)
    (hφd : DenseRange φ) (F : Set X) (hF : F.Finite)
    (hFc : ∀ x ∈ F, IsClosed ({x} : Set X)) (hfib : ∀ p ∉ F, (φ ⁻¹' {p}).Subsingleton) :
    {C : IrreducibleCloseds X' |
      topologicalKrullDim (C : Set X') = 1 ∧ ∃ p, φ '' C = {p}}.Finite := by
  have hZ : IsClosed (φ ⁻¹' F) := by
    refine IsClosed.preimage hφ ?_
    rw [← Set.biUnion_of_singleton F]
    exact hF.isClosed_biUnion hFc
  obtain ⟨Ss, hSf, hSc, hSi, hSU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine (hSf.preimage SetLike.coe_injective.injOn).subset ?_
  rintro C ⟨hC1, p, hp⟩
  have hCns : ¬ (C : Set X').Subsingleton := by
    intro hs
    have : Subsingleton (C : Set X') := hs.coe_sort
    have := topologicalKrullDim_zero_of_discreteTopology (C : Set X')
    rw [hC1] at this
    exact absurd this (by decide)
  have hCp : (C : Set X') ⊆ φ ⁻¹' {p} := fun x hx => hp ▸ Set.mem_image_of_mem φ hx
  have hpF : p ∈ F := by
    by_contra hpF
    exact hCns ((hfib p hpF).anti hCp)
  have hCZ : (C : Set X') ⊆ ⋃₀ Ss :=
    hSU ▸ hCp.trans (Set.preimage_mono (Set.singleton_subset_iff.mpr hpF))
  obtain ⟨t, htS, hCt⟩ : ∃ t ∈ Ss, (C : Set X') ⊆ t := by
    have := (isIrreducible_iff_sUnion_isClosed.mp C.isIrreducible) hSf.toFinset
      (by simpa using hSc) (by simpa using hCZ)
    simpa using this
  have htZ : t ⊆ φ ⁻¹' F := hSU ▸ Set.subset_sUnion_of_mem htS
  obtain ⟨q, hqF, htq⟩ : ∃ q ∈ F, φ '' t ⊆ {q} := by
    have hirr := (hSi t htS).image φ hφ.continuousOn
    have := (isIrreducible_iff_sUnion_isClosed.mp hirr) (hF.toFinset.image fun x => {x})
      (by simpa using hFc) (by
        rintro _ ⟨x, hx, rfl⟩
        simpa using htZ hx)
    obtain ⟨q, hq, htq⟩ : ∃ q ∈ F, t ⊆ φ ⁻¹' {q} := by simpa using this
    exact ⟨q, hq, Set.image_subset_iff.mpr htq⟩
  show (C : Set X') ∈ Ss
  by_contra hne
  let T : IrreducibleCloseds X' := ⟨t, hSi t htS, hSc t htS⟩
  have hlt : C < T := lt_of_le_of_ne hCt (fun h => hne (h ▸ htS))
  have h1 : ((1 : ℕ∞) : WithBot ℕ∞) ≤ Order.height C := by
    have := topologicalKrullDim_le_height C
    rw [hC1] at this
    exact this
  have h2 : Order.height C + 1 ≤ Order.height T := Order.height_add_one_le hlt
  have h3 : Order.height T + Order.coheight T ≤ 2 := by
    have : Nonempty (IrreducibleCloseds X') := ⟨T⟩
    have := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := IrreducibleCloseds X')
    rw [← topologicalKrullDim, hdim] at this
    have h := le_iSup (fun a : IrreducibleCloseds X' => Order.height a + Order.coheight a) T
    exact WithBot.coe_le_coe.mp (((WithBot.coe_le_coe.mpr h).trans this.symm.le).trans_eq rfl)
  have hT0 : Order.coheight T = 0 := by
    have h1' : 1 ≤ Order.height C := WithBot.coe_le_coe.mp h1
    have hT2 : (2 : ℕ∞) ≤ Order.height T := by
      calc
        (2 : ℕ∞) = 1 + 1 := one_add_one_eq_two.symm
        _ ≤ Order.height C + 1 := by gcongr
        _ ≤ Order.height T := h2
    have h4 : 2 + Order.coheight T ≤ 2 := le_trans (by gcongr) h3
    generalize Order.coheight T = c at h4 ⊢
    induction c using ENat.recTopCoe with
    | top => simp at h4
    | coe n =>
      norm_cast at h4 ⊢
      omega
  have hTmax : IsMax T := Order.coheight_eq_zero.mp hT0
  have htuniv : t = Set.univ := by
    let U : IrreducibleCloseds X' :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X', isClosed_univ⟩
    have hTU : T ≤ U := fun x _ => trivial
    have hTU' : T = U := le_antisymm hTU (hTmax hTU)
    exact congrArg SetLike.coe hTU'
  have hrange : Set.range φ ⊆ {q} := by
    rintro _ ⟨x, rfl⟩
    exact htq ⟨x, htuniv ▸ trivial, rfl⟩
  have huniv : (Set.univ : Set X) ⊆ {q} := by
    rw [← hφd.closure_range]
    exact closure_minimal hrange (hFc q hqF)
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  exact hab ((huniv trivial).trans (huniv trivial).symm)


/-! ### Regular schemes are normal -/

/-- A regular scheme is normal. -/
theorem isNormal_of_isRegular {X : Scheme.{u}} (hX : X.IsRegular) : IsNormal X := by
  obtain ⟨hLN, hreg⟩ := hX
  have key : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hloc' : ∀ y : PrimeSpectrum Γ(X, U),
        IsRegularLocalRing (Localization.AtPrime y.asIdeal) := by
      intro y
      obtain ⟨z, hz⟩ : ∃ z : U, hU.primeIdealOf z = y :=
        ⟨⟨hU.fromSpec y, hU.range_fromSpec.subset ⟨y, rfl⟩⟩,
          hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)⟩
      subst hz
      let := X.presheaf.algebra_section_stalk z
      have := hU.isLocalization_stalk z
      have : IsRegularLocalRing (X.presheaf.stalk z.1) := hreg _
      exact IsRegularLocalRing.of_ringEquiv
        (IsLocalization.algEquiv (hU.primeIdealOf z).asIdeal.primeCompl (X.presheaf.stalk z.1)
          (Localization.AtPrime (hU.primeIdealOf z).asIdeal)).toRingEquiv
    have hloc : ∀ (Q : Ideal Γ(X, U)) [Q.IsPrime],
        IsRegularLocalRing (Localization.AtPrime Q) := fun Q _ => hloc' ⟨Q, ‹_›⟩
    have hN := (SerreNormality.normal_iff_R1_and_S2 Γ(X, U)).mpr
      ⟨fun Q _ _ => hloc Q, fun Q _ hQ => by
        have := hloc Q
        have hcm := IsRegularLocalRing.isCohenMacaulayLocalRing (Localization.AtPrime Q)
        have h := hcm.depth_eq_ringKrullDim
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)] at h
        rw [WithBot.coe_inj.mp h]
        exact hQ⟩
    let P := hU.primeIdealOf ⟨x, hxU⟩
    let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    obtain ⟨hd, hic⟩ := hN P.asIdeal
    let e := IsLocalization.algEquiv P.asIdeal.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime P.asIdeal)
    exact ⟨e.toRingEquiv.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm.toRingEquiv⟩
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩


/-! ### The fibres over the domain of the inverse -/

namespace SchemeRationalMap

/-- A partial map whose underlying morphism is the inclusion of its domain is
equivalent to the identity. -/
theorem equiv_id_of_hom_eq_ι {X : Scheme.{u}} (F : X.PartialMap X) (h : F.hom = F.domain.ι) :
    F.equiv (Scheme.PartialMap.id X) := by
  refine ⟨F.domain, F.dense_domain, le_rfl, le_top, ?_⟩
  change X.homOfLE le_rfl ≫ F.hom = X.homOfLE le_top ≫ X.topIso.hom ≫ 𝟙 X
  simp [h]

/-- A partial isomorphism followed by its inverse is the identity rational map. -/
theorem partialIso_toRationalMap_comp_symm {X Y : Scheme.{u}} [IrreducibleSpace X] [Nonempty Y]
    (e : X.PartialIso Y) [IsDominant e.toPartialMap.hom] :
    e.toRationalMap.comp e.symm.toRationalMap = Scheme.RationalMap.id X := by
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.PartialMap.toRationalMap_eq_iff]
  refine equiv_id_of_hom_eq_ι _ ?_
  have h1 : (e.iso.hom ≫ e.target.ι) ∣_ e.target ≫ e.iso.inv =
      ((e.iso.hom ≫ e.target.ι) ⁻¹ᵁ e.target).ι := by
    rw [← cancel_mono e.iso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← cancel_mono e.target.ι, morphismRestrict_ι, Category.assoc]
  refine (cancel_epi (Scheme.Hom.isoImage e.toPartialMap.domain.ι
    (e.toPartialMap.hom ⁻¹ᵁ e.symm.toPartialMap.domain)).hom).mp ?_
  simp only [Scheme.PartialMap.comp_hom, Iso.hom_inv_id_assoc]
  refine Eq.trans ?_ (Scheme.Hom.isoImage_hom_ι _ _).symm
  exact (reassoc_of% h1) e.source.ι

/-- **Key step.** Let `f : X' ⟶ X` be dominant, with `X'` integral and separated, and
let `T : X ⤏ X'` satisfy `T ∘ f = id` as rational maps. If `p ∈ Dom(T)`, then the fibre
of `f` over `p` has at most one point. -/
theorem subsingleton_preimage_of_mem_dom {X' X : Scheme.{u}} [IsIntegral X'] [X'.IsSeparated]
    [Nonempty X] (f : X' ⟶ X) [IsDominant f] (T : X ⤏ X')
    (hT : f.toRationalMap.comp T = Scheme.RationalMap.id X') {p : X} (hp : p ∈ dom T) :
    (f.base ⁻¹' {p}).Subsingleton := by
  obtain ⟨g, hpg, hg⟩ := mem_dom_iff.mp hp
  set F := f.toPartialMap.comp g with hFdef
  have hFeq : F.equiv ((Scheme.PartialMap.id X').restrict F.domain F.dense_domain le_top) := by
    have h1 : F.toRationalMap = (Scheme.PartialMap.id X').toRationalMap := by
      rw [← Scheme.RationalMap.toRationalMap_comp, hg, hT]
    exact (Scheme.PartialMap.toRationalMap_eq_iff.mp h1).trans
      ((Scheme.PartialMap.id X').restrict_equiv _ _ _).symm
  obtain ⟨W, hW, hWl, hWr, e⟩ := hFeq
  have hFid : F.hom = F.domain.ι := by
    have : IsDominant (X'.homOfLE hWl) := AlgebraicGeometry.Opens.isDominant_homOfLE hW hWl
    refine ext_of_isDominant (X'.homOfLE hWl) ?_
    have e' : X'.homOfLE hWl ≫ F.hom =
        X'.homOfLE hWr ≫ X'.homOfLE le_top ≫ X'.topIso.hom ≫ 𝟙 X' := e
    rw [e']
    simp
  let q : F.domain.toScheme ⟶ g.domain.toScheme :=
    (Scheme.Hom.isoImage _ _).inv ≫ f.toPartialMap.hom ∣_ g.domain
  have hFq : F.hom = q ≫ g.hom := rfl
  have hq' : (Scheme.Hom.isoImage f.toPartialMap.domain.ι
      (f.toPartialMap.hom ⁻¹ᵁ g.domain)).inv ≫ f.toPartialMap.hom ∣_ g.domain ≫ g.domain.ι =
      (f.toPartialMap.domain.ι ''ᵁ (f.toPartialMap.hom ⁻¹ᵁ g.domain)).ι ≫ f := by
    rw [← cancel_epi (Scheme.Hom.isoImage f.toPartialMap.domain.ι
      (f.toPartialMap.hom ⁻¹ᵁ g.domain)).hom, Iso.hom_inv_id_assoc, morphismRestrict_ι,
      Scheme.Hom.isoImage_hom_ι_assoc]
    simp only [Scheme.Hom.toPartialMap_hom, Scheme.topIso_hom]
    rfl
  have hq : q ≫ g.domain.ι = F.domain.ι ≫ f := (Category.assoc _ _ _).trans hq'
  have hmem : ∀ x ∈ f.base ⁻¹' {p}, x ∈ F.domain := by
    intro x hx
    refine ⟨⟨x, trivial⟩, ?_, rfl⟩
    show f.base x ∈ g.domain
    exact (hx : f.base x = p) ▸ hpg
  intro x hx y hy
  let x' : F.domain.toScheme := ⟨x, hmem x hx⟩
  let y' : F.domain.toScheme := ⟨y, hmem y hy⟩
  have hqxy : q x' = q y' := by
    apply g.domain.ι.isOpenEmbedding.injective
    have hx' := congr(($hq) x')
    have hy' := congr(($hq) y')
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hx' hy'
    rw [hx', hy']
    exact (hx : f.base x = p).trans (hy : f.base y = p).symm
  have hx' := congr(($hFid) x')
  have hy' := congr(($hFid) y')
  rw [hFq, Scheme.Hom.comp_apply] at hx' hy'
  have hxy : F.domain.ι x' = F.domain.ι y' := by rw [← hx', ← hy', hqxy]
  exact hxy

end SchemeRationalMap

/-! ### Contracted curves -/

/-- The irreducible curves of `X'` contracted by `f : X' ⟶ X`: the irreducible closed subsets
of `X'` of dimension one whose image under `f` is a single point. -/
def contractedCurves {X' X : Scheme.{u}} (f : X' ⟶ X) : Set (IrreducibleCloseds X') :=
  {C | topologicalKrullDim (C : Set X') = 1 ∧ ∃ p : X, f.base '' C = {p}}

/-- **Hartshorne V.5, Corollary 5.4.** The number `n(f)` of irreducible curves of `X'`
contracted by `f : X' ⟶ X`. -/
noncomputable def numContractedCurves {X' X : Scheme.{u}} (f : X' ⟶ X) : ℕ :=
  (contractedCurves f).ncard

variable {k : Type u} [Field k] {X' X : Scheme.{u}} [X'.Over (Spec (.of k))]
  [X.Over (Spec (.of k))]

/-- **Hartshorne V.5, Corollary 5.4, first part, general form.** Let `f : X' ⟶ X` be a
birational morphism of projective surfaces over `k`, with `X` normal. Then only finitely many
irreducible curves of `X'` are mapped to points by `f`. -/
theorem contractedCurves_finite_of_isNormal [IsIntegral X'] [IsIntegral X] [IsNormal X]
    (hX' : Projective (X' ↘ Spec (.of k))) (hX : Projective (X ↘ Spec (.of k)))
    (hdim' : topologicalKrullDim X' = 2) (hdim : topologicalKrullDim X = 2) (f : X' ⟶ X)
    (hf : ∃ e : X'.PartialIso X,
      e.IsOver (X' ↘ Spec (.of k)) (X ↘ Spec (.of k)) ∧ e.toRationalMap = f.toRationalMap) :
    (contractedCurves f).Finite := by
  obtain ⟨e, he, hef⟩ := hf
  have := hX'.isProper
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (X' ↘ Spec (.of k))
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (X' ↘ Spec (.of k))
  have : IsNoetherian X' := {}
  have : X'.IsSeparated := ⟨by rw [← terminal.comp_from (X' ↘ Spec (.of k))]; infer_instance⟩
  have hedom : IsDominant e.toPartialMap.hom := by
    have : IsDominant e.target.ι := AlgebraicGeometry.Opens.isDominant_ι e.dense_target
    show IsDominant (e.iso.hom ≫ e.target.ι)
    infer_instance
  have hfdom : IsDominant f := by
    have h1 : f.toPartialMap.equiv e.toPartialMap :=
      Scheme.PartialMap.toRationalMap_eq_iff.mp hef.symm
    have : IsDominant (X'.topIso.hom ≫ f) :=
      (Scheme.PartialMap.isDominant_hom_iff_of_equiv _ _ h1).mpr hedom
    exact IsDominant.of_comp X'.topIso.hom f
  have hT : f.toRationalMap.comp e.symm.toRationalMap = Scheme.RationalMap.id X' := by
    have key : ∀ (φ : X' ⤏ X) [φ.IsDominant], φ = e.toRationalMap →
        φ.comp e.symm.toRationalMap = Scheme.RationalMap.id X' := by
      rintro φ _ rfl
      exact SchemeRationalMap.partialIso_toRationalMap_comp_symm e
    exact key _ hef.symm
  obtain ⟨hFfin, hFcl⟩ := SchemeRationalMap.normal_projective_surface_fundamentalLocus_finite
    hX hX' hdim e.symm.toRationalMap ⟨e.symm, he.symm, rfl⟩
  have : Nontrivial X := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have := topologicalKrullDim_zero_of_discreteTopology X
    rw [hdim] at this
    exact absurd this (by decide)
  exact finite_contracted_of_subsingleton_fibres hdim' f.base f.continuous hfdom.denseRange _
    hFfin hFcl fun p hp =>
      SchemeRationalMap.subsingleton_preimage_of_mem_dom f e.symm.toRationalMap hT
        (not_not.mp hp)

/-- **Hartshorne V.5, Corollary 5.4, first part.** Let `f : X' ⟶ X` be a birational morphism
of nonsingular projective surfaces over `k`. Then only finitely many irreducible curves of `X'`
are mapped to points by `f`; their number is `n(f) = numContractedCurves f`. -/
theorem contractedCurves_finite [IsIntegral X'] [IsIntegral X] (hX'reg : X'.IsRegular)
    (hXreg : X.IsRegular) (hX' : Projective (X' ↘ Spec (.of k)))
    (hX : Projective (X ↘ Spec (.of k))) (hdim' : topologicalKrullDim X' = 2)
    (hdim : topologicalKrullDim X = 2) (f : X' ⟶ X)
    (hf : ∃ e : X'.PartialIso X,
      e.IsOver (X' ↘ Spec (.of k)) (X ↘ Spec (.of k)) ∧ e.toRationalMap = f.toRationalMap) :
    (contractedCurves f).Finite := by
  have := isNormal_of_isRegular hXreg
  exact contractedCurves_finite_of_isNormal hX' hX hdim' hdim f hf

end Hartshorne
