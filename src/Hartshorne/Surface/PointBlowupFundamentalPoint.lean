/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.PointMonoidalTransformation
import Hartshorne.Rational.SchemeGraphTotalTransform
import Hartshorne.Scheme.DimensionAtClosedPoint
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# The center of a monoidal transformation is the fundamental point of its inverse

Hartshorne, *Algebraic Geometry*, V.5, Example 5.1.1 (p. 410).

Let `X` be a surface, `P` a closed point and `π : X̃ ⟶ X` the monoidal transformation with
center `P`, with exceptional divisor `E = π⁻¹(P)`. The isomorphism `X̃ - E ≅ X - P` induced by `π`
is a partial isomorphism `X̃ ⇢ X`, whose rational map is that of `π`; its inverse is the inverse
birational transformation `T : X ⇢ X̃`. Then:

* `π` is defined everywhere: `Dom(π) = X̃`;
* `Dom(T) = X - P`, so `P` is the unique fundamental point of `T`;
* the total transform of `{P}` under `T` is the exceptional curve, i.e. the support of `E`, the
  fibre `π⁻¹(P)`. More generally `T(Z) = π⁻¹(Z)` for every subset `Z` of `X`.

Here the exceptional curve is understood set-theoretically, as the support of the effective
Cartier divisor `E`; that `E` is a curve isomorphic to `ℙ¹` is a separate result.

## Proof

The rational map `T` is defined on `X - P`. If it were defined at `P`, it would be defined on all
of `X`, by a morphism `σ : X ⟶ X̃`. Both `σ ≫ π` and `π ≫ σ` agree with the identity on the dense
open subsets `X - P` and `X̃ - E`; as the schemes are reduced and separated, `π` would be an
isomorphism. Then `E = π⁻¹(P)` would be a single point `e`, with `dim 𝒪_{X̃,e} = dim 𝒪_{X,P} = 2`.
But `E` is an effective Cartier divisor: near `e` it is cut out by one element `g` of an affine
coordinate ring, and the prime of `e` is minimal over `(g)`, so it has height at most one by
Krull's principal ideal theorem. This contradiction shows `P ∉ Dom(T)`.

For the total transform, the graph of `T` over `X - P` lies in the transposed graph
`{(π(y), y)}` of `π`, which is closed in `X ×_k X̃` because `X` is separated over `k`; and it
contains the image of the dense open set `X̃ - E` of `X̃`. So the closure `Γ_T` is exactly the
transposed graph of `π`, and `p₂(p₁⁻¹(Z)) = π⁻¹(Z)`.

## Main definitions and results

* `Hartshorne.Surface.pointBlowupPartialIso`: the partial isomorphism `X̃ ⇢ X` given by `π`.
* `Hartshorne.Surface.toRationalMap_pointBlowupProjection`: it represents the rational map of `π`.
* `Hartshorne.Surface.pointBlowupInverse`: the inverse birational transformation `T : X ⇢ X̃`.
* `Hartshorne.Surface.dom_toRationalMap_pointBlowupProjection`: `π` is defined everywhere.
* `Hartshorne.Surface.dom_pointBlowupInverse`: `Dom(T) = X - P`.
* `Hartshorne.Surface.fundamentalPoints_pointBlowupInverse`: `P` is the fundamental point of `T`.
* `Hartshorne.Surface.totalTransform_pointBlowupInverse_singleton`: `T(P) = E` as sets.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.CartierDivisor

/-- **Krull's principal ideal theorem for an effective Cartier divisor.** On a locally Noetherian
scheme, a point `x` of the support of an effective Cartier divisor which has no proper
generalization inside the support has codimension at most one: near `x` the divisor is cut out
by one element `g` of an affine coordinate ring, and the prime of `x` is minimal over `(g)`. -/
theorem coheight_le_one_of_minimal_mem_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    {D : X.CartierDivisor} (hD : D.IsEffective) {x : X} (hx : x ∈ (idealSheafData hD).support)
    (hmin : ∀ y ∈ (idealSheafData hD).support, y ⤳ x → y = x) :
    Order.coheight x ≤ 1 := by
  set I := idealSheafData hD
  obtain ⟨W, hxW, g, -, hIW⟩ := isLocallyPrincipalNonZeroDivisor_idealSheafData hD x
  have hW : IsAffineOpen (W : X.Opens) := W.2
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  set p := hW.primeIdealOf ⟨x, hxW⟩
  have hpx : hW.fromSpec p = x := hW.fromSpec_primeIdealOf ⟨x, hxW⟩
  -- a point of `Spec Γ(X, W)` lies on the support exactly when its prime contains `g`
  have hmem : ∀ Q : PrimeSpectrum Γ(X, W), hW.fromSpec Q ∈ I.support ↔ g ∈ Q.asIdeal := by
    intro Q
    have hQW : hW.fromSpec Q ∈ (W : X.Opens) := hW.range_fromSpec.subset ⟨Q, rfl⟩
    rw [I.mem_support_iff_of_mem (U := W) hQW]
    change Q ∈ hW.fromSpec ⁻¹' X.zeroLocus (I.ideal W : Set Γ(X, W)) ↔ _
    rw [hW.fromSpec_preimage_zeroLocus]
    change (I.ideal W : Set Γ(X, W)) ⊆ Q.asIdeal ↔ _
    rw [hIW, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
  have hgp : g ∈ p.asIdeal := (hmem p).1 (hpx ▸ hx)
  -- `p` is minimal over `(g)`
  have hminp : p.asIdeal ∈ (Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hgp⟩, fun Q hQ hQp => ?_⟩
    let Q' : PrimeSpectrum Γ(X, W) := ⟨Q, hQ.1⟩
    have hgQ : g ∈ Q'.asIdeal := (Ideal.span_singleton_le_iff_mem _).1 hQ.2
    have h₁ : hW.fromSpec Q' ⤳ x :=
      hpx ▸ ((PrimeSpectrum.le_iff_specializes Q' p).1 hQp).map hW.fromSpec.continuous
    have h₃ : Q' = p :=
      hW.fromSpec.isOpenEmbedding.injective ((hmin _ ((hmem Q').2 hgQ) h₁).trans hpx.symm)
    rw [← h₃]
  rw [← hpx]
  calc Order.coheight (hW.fromSpec p) = Order.coheight (show Spec Γ(X, W) from p) :=
        coheight_eq_of_isOpenImmersion _
    _ = p.asIdeal.height := (idealHeight_eq_coheight _ p).symm
    _ ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hminp

end AlgebraicGeometry.Scheme.CartierDivisor

namespace Hartshorne

noncomputable section

namespace Surface

open SchemeRationalMap

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Surface k) (P : S.Point)

/-! ### Preliminaries on the monoidal transformation -/

/-- The monoidal transformation `X̃` is separated: it is projective over `k`. -/
instance isSeparated_pointBlowup : (S.pointBlowup P).IsSeparated := by
  have : IsProper (S.pointBlowupProjection P ≫ S.hom) := (S.pointBlowup_projective P).2.2.isProper
  constructor
  rw [Subsingleton.elim (terminal.from (S.pointBlowup P))
    ((S.pointBlowupProjection P ≫ S.hom) ≫ terminal.from (Spec (.of k)))]
  infer_instance

/-- The monoidal transformation `X̃` is locally Noetherian: it is of finite type over `k`. -/
instance isLocallyNoetherian_pointBlowup : IsLocallyNoetherian (S.pointBlowup P) := by
  have : IsProper (S.pointBlowupProjection P ≫ S.hom) := (S.pointBlowup_projective P).2.2.isProper
  exact LocallyOfFiniteType.isLocallyNoetherian (S.pointBlowupProjection P ≫ S.hom)

/-- `X - P` is dense in the surface. -/
theorem dense_pointCompl : Dense (S.pointCompl P : Set S.X) := by
  obtain ⟨x, hx⟩ := S.exists_ne_point P
  exact (S.pointCompl P).2.dense ⟨x, hx⟩

/-- `X̃ - E` is dense in the monoidal transformation. -/
theorem dense_pointBlowupExceptionalCompl :
    Dense (S.pointBlowupExceptionalCompl P : Set (S.pointBlowup P)) := by
  obtain ⟨x, hx⟩ := S.exists_ne_point P
  exact (S.pointBlowupExceptionalCompl P).2.dense
    ⟨_, ((S.pointBlowupIsoOffCenter P).inv ⟨x, hx⟩).2⟩

@[reassoc]
theorem pointBlowupIsoOffCenter_inv_ι_comp :
    (S.pointBlowupIsoOffCenter P).inv ≫ (S.pointBlowupExceptionalCompl P).ι ≫
      S.pointBlowupProjection P = (S.pointCompl P).ι := by
  rw [← pointBlowupIsoOffCenter_hom_ι, Iso.inv_hom_id_assoc]

/-! ### The birational transformation and its inverse -/

/-- **The monoidal transformation as a partial isomorphism** `X̃ ⇢ X`: the isomorphism
`X̃ - E ≅ X - P` induced by `π` between dense open subschemes. -/
def pointBlowupPartialIso : (S.pointBlowup P).PartialIso S.X where
  source := S.pointBlowupExceptionalCompl P
  dense_source := S.dense_pointBlowupExceptionalCompl P
  target := S.pointCompl P
  dense_target := S.dense_pointCompl P
  iso := S.pointBlowupIsoOffCenter P

/-- The partial isomorphism `X̃ ⇢ X` represents the rational map of `π`: `π` is the birational
transformation given by the isomorphism `X̃ - E ≅ X - P`. -/
theorem toRationalMap_pointBlowupProjection :
    (S.pointBlowupProjection P).toRationalMap = (S.pointBlowupPartialIso P).toRationalMap := by
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨S.pointBlowupExceptionalCompl P, S.dense_pointBlowupExceptionalCompl P, le_top, le_rfl,
    ?_⟩
  change (S.pointBlowup P).homOfLE le_top ≫ (S.pointBlowup P).topIso.hom ≫ _ =
    (S.pointBlowup P).homOfLE le_rfl ≫ (S.pointBlowupIsoOffCenter P).hom ≫ (S.pointCompl P).ι
  rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_rfl, Category.id_comp,
    pointBlowupIsoOffCenter_hom_ι]

/-- **The inverse birational transformation** `T : X ⇢ X̃` of the monoidal transformation: the
rational map given by the inverse of the isomorphism `X̃ - E ≅ X - P`. -/
def pointBlowupInverse : S.X ⤏ S.pointBlowup P :=
  (S.pointBlowupPartialIso P).symm.toRationalMap

/-- `π ∘ T` is the identity rational map of `X`. -/
theorem pointBlowupInverse_compHom :
    (S.pointBlowupInverse P).compHom (S.pointBlowupProjection P) = Scheme.RationalMap.id S.X := by
  rw [pointBlowupInverse, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨S.pointCompl P, S.dense_pointCompl P, le_rfl, le_top, ?_⟩
  change S.X.homOfLE le_rfl ≫ ((S.pointBlowupIsoOffCenter P).inv ≫
      (S.pointBlowupExceptionalCompl P).ι) ≫ S.pointBlowupProjection P =
    S.X.homOfLE le_top ≫ S.X.topIso.hom ≫ 𝟙 S.X
  rw [Scheme.homOfLE_rfl, Category.id_comp, Category.assoc, pointBlowupIsoOffCenter_inv_ι_comp,
    Scheme.topIso_hom, Category.comp_id, Scheme.homOfLE_ι]

/-- **`π` is defined everywhere** (Hartshorne V.5, Example 5.1.1): the maximal domain of its
rational map is all of `X̃`. -/
theorem dom_toRationalMap_pointBlowupProjection :
    dom (S.pointBlowupProjection P).toRationalMap = ⊤ :=
  top_le_iff.mp (le_dom (S.pointBlowupProjection P).toPartialMap rfl)

/-- The inverse birational transformation is defined on `X - P`. -/
theorem pointCompl_le_dom_pointBlowupInverse : S.pointCompl P ≤ dom (S.pointBlowupInverse P) :=
  le_dom (S.pointBlowupPartialIso P).symm.toPartialMap rfl

/-- On `X - P` the glued morphism of `T` is the inverse of the isomorphism `X̃ - E ≅ X - P`. -/
theorem homOfLE_domHom_pointBlowupInverse :
    S.X.homOfLE (S.pointCompl_le_dom_pointBlowupInverse P) ≫ domHom (S.pointBlowupInverse P) =
      (S.pointBlowupIsoOffCenter P).inv ≫ (S.pointBlowupExceptionalCompl P).ι :=
  homOfLE_domHom _ rfl

/-- `T ∘ π` is the identity on `X̃ - E`. -/
theorem pointBlowupIsoOffCenter_hom_comp_domHom :
    (S.pointBlowupIsoOffCenter P).hom ≫
        S.X.homOfLE (S.pointCompl_le_dom_pointBlowupInverse P) ≫
          domHom (S.pointBlowupInverse P) =
      (S.pointBlowupExceptionalCompl P).ι := by
  rw [homOfLE_domHom_pointBlowupInverse, Iso.hom_inv_id_assoc]

/-- `π ∘ T` is the inclusion on all of `Dom(T)`. -/
@[reassoc]
theorem domHom_pointBlowupInverse_comp :
    domHom (S.pointBlowupInverse P) ≫ S.pointBlowupProjection P =
      (dom (S.pointBlowupInverse P)).ι := by
  have : IsDominant (S.X.homOfLE (S.pointCompl_le_dom_pointBlowupInverse P)) :=
    Opens.isDominant_homOfLE (S.dense_pointCompl P) _
  refine ext_of_isDominant (S.X.homOfLE (S.pointCompl_le_dom_pointBlowupInverse P)) ?_
  rw [reassoc_of% (S.homOfLE_domHom_pointBlowupInverse P), pointBlowupIsoOffCenter_inv_ι_comp,
    Scheme.homOfLE_ι]

/-! ### The center is the fundamental point -/

/-- **The monoidal transformation is not an isomorphism.** Otherwise `E = π⁻¹(P)` would be a single
point `e` of the support of the effective Cartier divisor `E`, of codimension at most one by
Krull's principal ideal theorem, whereas `dim 𝒪_{X̃,e} = dim 𝒪_{X,P} = 2`. -/
theorem not_isIso_pointBlowupProjection : ¬ IsIso (S.pointBlowupProjection P) := by
  intro hiso
  set π := S.pointBlowupProjection P
  set e : S.pointBlowup P := inv π P.1
  have hπe : π e = P.1 := by
    change (inv π ≫ π) P.1 = P.1
    rw [IsIso.inv_hom_id]
    rfl
  have hinj : Function.Injective π := π.isOpenEmbedding.injective
  have hsupp : ∀ y, y ∈ (Scheme.CartierDivisor.idealSheafData
      (S.pointBlowupExceptional_isEffective P)).support ↔ π y = P.1 := by
    intro y
    rw [← SetLike.mem_coe, coe_support_pointBlowupExceptional]
    rfl
  have hle := Scheme.CartierDivisor.coheight_le_one_of_minimal_mem_support
    (S.pointBlowupExceptional_isEffective P) ((hsupp e).2 hπe)
    (fun y hy _ => hinj (((hsupp y).1 hy).trans hπe.symm))
  have h2 : Order.coheight (π e) = 2 := by
    rw [hπe]
    have h := dimension_at_closed_point S.hom S.finiteType P.1 P.2
    rw [S.dim_eq, ringKrullDim_stalk_eq_coheight] at h
    have h' : ((Order.coheight P.1 : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := h.symm
    exact WithBot.coe_injective h'
  rw [coheight_eq_of_isOpenImmersion] at h2
  rw [h2] at hle
  exact absurd hle (by norm_num)

/-- **The inverse transformation is defined exactly away from the center** (Hartshorne V.5,
Example 5.1.1): `Dom(T) = X - P`. -/
theorem dom_pointBlowupInverse : dom (S.pointBlowupInverse P) = S.pointCompl P := by
  refine le_antisymm (fun x hx => ?_) (S.pointCompl_le_dom_pointBlowupInverse P)
  by_contra hxP
  have hxP' : x = P.1 := by simpa [pointCompl] using hxP
  subst hxP'
  have htop : ⊤ ≤ dom (S.pointBlowupInverse P) := fun y _ => by
    by_cases hy : y = P.1
    · exact hy ▸ hx
    · exact S.pointCompl_le_dom_pointBlowupInverse P hy
  refine S.not_isIso_pointBlowupProjection P ⟨S.X.topIso.inv ≫ S.X.homOfLE htop ≫
    domHom (S.pointBlowupInverse P), ?_, ?_⟩
  · have : IsDominant (S.pointBlowupExceptionalCompl P).ι :=
      Opens.isDominant_ι (S.dense_pointBlowupExceptionalCompl P)
    refine ext_of_isDominant (S.pointBlowupExceptionalCompl P).ι ?_
    have h : (S.pointCompl P).ι ≫ S.X.topIso.inv = S.X.homOfLE le_top := by
      rw [Iso.comp_inv_eq, Scheme.topIso_hom, Scheme.homOfLE_ι]
    rw [Category.comp_id, ← pointBlowupIsoOffCenter_hom_ι_assoc, reassoc_of% h,
      Scheme.homOfLE_homOfLE_assoc]
    exact S.pointBlowupIsoOffCenter_hom_comp_domHom P
  · rw [Category.assoc, Category.assoc, domHom_pointBlowupInverse_comp, Scheme.homOfLE_ι,
      Scheme.toIso_inv_ι]

/-- The fundamental locus of `T` is the center `{P}`. -/
theorem coe_fundamentalLocus_pointBlowupInverse :
    (fundamentalLocus (S.pointBlowupInverse P) : Set S.X) = {P.1} := by
  rw [coe_fundamentalLocus, dom_pointBlowupInverse]
  exact compl_compl _

/-- **The center is the fundamental point of the inverse** (Hartshorne V.5, Example 5.1.1): `P` is
the unique fundamental point of `T`. -/
theorem fundamentalPoints_pointBlowupInverse :
    fundamentalPoints (S.pointBlowupInverse P) = {P.1} := by
  ext x
  rw [mem_fundamentalPoints, dom_pointBlowupInverse, Set.mem_singleton_iff]
  have h : x ∉ S.pointCompl P ↔ x = P.1 := ⟨fun h => not_not.mp h, fun h h' => h' h⟩
  rw [h]
  exact ⟨And.left, fun h => ⟨h, h ▸ P.2⟩⟩

/-! ### The total transform of the center -/

/-- The surface as a scheme over `k`, via its structure morphism. -/
abbrev overSpec : S.X.Over (Spec (.of k)) := ⟨S.hom⟩

/-- The monoidal transformation as a scheme over `k`, via `X̃ ⟶ X ⟶ Spec k`. -/
abbrev pointBlowupOverSpec : (S.pointBlowup P).Over (Spec (.of k)) :=
  ⟨S.pointBlowupProjection P ≫ S.hom⟩

attribute [local instance] overSpec pointBlowupOverSpec

/-- The inverse birational transformation is a rational map over `k`. -/
instance isOver_pointBlowupInverse : (S.pointBlowupInverse P).IsOver (Spec (.of k)) := by
  have : (S.pointBlowupPartialIso P).symm.toPartialMap.IsOver (Spec (.of k)) :=
    ⟨by
      change ((S.pointBlowupIsoOffCenter P).inv ≫ (S.pointBlowupExceptionalCompl P).ι) ≫
          S.pointBlowupProjection P ≫ S.hom = (S.pointCompl P).ι ≫ S.hom
      rw [Category.assoc, pointBlowupIsoOffCenter_inv_ι_comp_assoc]⟩
  exact inferInstanceAs ((S.pointBlowupPartialIso P).symm.toPartialMap.toRationalMap.IsOver _)

/-- **The total transform under the inverse is the inverse image under `π`.** The graph `Γ_T` is
the transposed graph `{(π(y), y)}` of `π`, so `T(Z) = π⁻¹(Z)` for every subset `Z` of `X`. -/
theorem totalTransform_pointBlowupInverse (Z : Set S.X) :
    totalTransform k (S.pointBlowupInverse P) Z = S.pointBlowupProjection P ⁻¹' Z := by
  set T := S.pointBlowupInverse P
  set π := S.pointBlowupProjection P
  -- the transposed graph `y ↦ (π(y), y)`, a closed immersion
  let τ₀ : S.pointBlowup P ⟶ pullback (S.pointBlowup P ↘ Spec (.of k)) (S.X ↘ Spec (.of k)) :=
    pullback.lift (𝟙 _) π (Category.id_comp _)
  let τ : S.pointBlowup P ⟶ pullback (S.X ↘ Spec (.of k)) (S.pointBlowup P ↘ Spec (.of k)) :=
    τ₀ ≫ (pullbackSymmetry _ _).hom
  have hτ₁ : τ ≫ pullback.fst _ _ = π := by
    simp only [τ, τ₀, Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullback.lift_snd _ _ _
  have hτ₂ : τ ≫ pullback.snd _ _ = 𝟙 _ := by
    simp only [τ, τ₀, Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullback.lift_fst _ _ _
  have : IsClosedImmersion τ₀ :=
    (inferInstance : IsClosedImmersion (pullback.lift (𝟙 (S.pointBlowup P)) π
      (Category.id_comp (π ≫ S.hom))))
  have : IsClosedImmersion τ := inferInstanceAs (IsClosedImmersion (τ₀ ≫ _))
  have hclosed : IsClosed (Set.range τ) := τ.isClosedEmbedding.isClosed_range
  have hgraph : graphHom k T = domHom T ≫ τ := by
    refine pullback.hom_ext ?_ ?_
    · rw [graphHom_fst, Category.assoc, hτ₁, domHom_pointBlowupInverse_comp]
    · rw [graphHom_snd, Category.assoc, hτ₂, Category.comp_id]
  have hrange : Set.range (graphClosureι k T) = Set.range τ := by
    rw [range_graphClosureι]
    refine subset_antisymm (closure_minimal ?_ hclosed) ?_
    · rintro _ ⟨d, rfl⟩
      exact ⟨domHom T d, by rw [hgraph]; rfl⟩
    · rintro _ ⟨y, rfl⟩
      have hy : y ∈ closure (S.pointBlowupExceptionalCompl P : Set (S.pointBlowup P)) := by
        rw [(S.dense_pointBlowupExceptionalCompl P).closure_eq]
        trivial
      refine closure_mono ?_ (image_closure_subset_closure_image τ.continuous ⟨y, hy, rfl⟩)
      rintro _ ⟨y', hy', rfl⟩
      refine ⟨S.X.homOfLE (S.pointCompl_le_dom_pointBlowupInverse P)
        ((S.pointBlowupIsoOffCenter P).hom ⟨y', hy'⟩), ?_⟩
      have key := congr($(S.pointBlowupIsoOffCenter_hom_comp_domHom P) ⟨y', hy'⟩)
      rw [hgraph]
      change τ (domHom T (S.X.homOfLE _ ((S.pointBlowupIsoOffCenter P).hom ⟨y', hy'⟩))) = τ y'
      exact congrArg τ key
  ext y
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨y', hy'⟩ : graphClosureι k T γ ∈ Set.range τ := hrange ▸ ⟨γ, rfl⟩
    have h₁ : graphFst k T γ = π y' := by
      change pullback.fst (S.X ↘ Spec (.of k)) (S.pointBlowup P ↘ Spec (.of k))
          (graphClosureι k T γ) = π y'
      rw [← hy', ← Scheme.Hom.comp_apply, hτ₁]
    have h₂ : graphSnd k T γ = y' := by
      change pullback.snd (S.X ↘ Spec (.of k)) (S.pointBlowup P ↘ Spec (.of k))
          (graphClosureι k T γ) = y'
      rw [← hy', ← Scheme.Hom.comp_apply, hτ₂]
      rfl
    rw [h₂]
    show π y' ∈ Z
    rw [← h₁]
    exact hγ
  · intro hy
    obtain ⟨γ, hγ⟩ : τ y ∈ Set.range (graphClosureι k T) := hrange ▸ ⟨y, rfl⟩
    refine ⟨γ, ?_, ?_⟩
    · change pullback.fst (S.X ↘ Spec (.of k)) (S.pointBlowup P ↘ Spec (.of k))
        (graphClosureι k T γ) ∈ Z
      rw [hγ, ← Scheme.Hom.comp_apply, hτ₁]
      exact hy
    · change pullback.snd (S.X ↘ Spec (.of k)) (S.pointBlowup P ↘ Spec (.of k))
        (graphClosureι k T γ) = y
      rw [hγ, ← Scheme.Hom.comp_apply, hτ₂]
      rfl

/-- **The total transform of the center is the exceptional curve** (Hartshorne V.5,
Example 5.1.1): `T(P)` is the support of the exceptional divisor `E`, the fibre `π⁻¹(P)`. -/
theorem totalTransform_pointBlowupInverse_singleton :
    totalTransform k (S.pointBlowupInverse P) {P.1} =
      ((Scheme.CartierDivisor.idealSheafData (S.pointBlowupExceptional_isEffective P)).support :
        Set (S.pointBlowup P)) := by
  rw [totalTransform_pointBlowupInverse, coe_support_pointBlowupExceptional]

end Surface

end

end Hartshorne
