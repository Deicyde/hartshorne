/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.SchemeMaximalDomain
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The graph and the total transform of a rational map

Hartshorne, *Algebraic Geometry*, V.5, the graph `Γ_T` and the total transform
`T(Z)` of a birational transformation, p. 410, in the language of schemes.

Let `X` and `Y` be schemes over a field `k` and let `T : X ⤏ Y` be a rational
map over `k`, with `X` reduced and `Y` separated, so that `T` is a morphism on
its maximal domain `Dom(T)`. The graph of `T` over `Dom(T)` is the morphism
`Dom(T) ⟶ X ×_k Y` with components the inclusion and the glued morphism
`Dom(T) ⟶ Y`. Its scheme-theoretic image is the closed subscheme `Γ_T` of
`X ×_k Y`, with the two projections `p₁ : Γ_T ⟶ X` and `p₂ : Γ_T ⟶ Y`. For a
subset `Z` of `X`, the total transform is the set `T(Z) = p₂(p₁⁻¹(Z))`.

Hartshorne's setting is a birational transformation of projective varieties
over `k`; such varieties are integral, hence reduced, Noetherian and separated,
and a birational transformation is in particular a rational map over `k`. The
constructions use only that `X` is reduced and `Y` is separated.

At a point `x` of `Dom(T)` the total transform of `{x}` is the single image
point of `x`. This uses that `X` is locally Noetherian (so the graph morphism is
quasi-compact and `Γ_T` has the closure of the graph as underlying set) and that
`Y` is separated (so the graph is closed above `Dom(T)`).

## Main definitions and results

* `Hartshorne.SchemeRationalMap.graphHom`: the graph `Dom(T) ⟶ X ×_k Y`.
* `Hartshorne.SchemeRationalMap.graphClosure`,
  `Hartshorne.SchemeRationalMap.graphClosureι`: the scheme-theoretic closure
  `Γ_T` of the graph and its closed immersion into `X ×_k Y`.
* `Hartshorne.SchemeRationalMap.graphFst`, `Hartshorne.SchemeRationalMap.graphSnd`:
  the projections `p₁`, `p₂`.
* `Hartshorne.SchemeRationalMap.totalTransform`: `T(Z) = p₂(p₁⁻¹(Z))`.
* `Hartshorne.SchemeRationalMap.totalTransform_singleton_of_mem_dom`,
  `Hartshorne.SchemeRationalMap.totalTransform_singleton_of_mem_dom_of_locallyOfFiniteType`:
  at a point of `Dom(T)` the total transform is the ordinary image point.
-/

namespace Hartshorne

namespace SchemeRationalMap

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))]

section

variable (k) [IsReduced X] [Y.IsSeparated] (T : X ⤏ Y) [T.IsOver (Spec (.of k))]

/-- The glued morphism `Dom(T) ⟶ Y` is a morphism over `k`. -/
theorem domHom_comp_over :
    domHom T ≫ Y ↘ Spec (.of k) = (dom T).ι ≫ X ↘ Spec (.of k) := by
  have : T.toPartialMap.IsOver (Spec (.of k)) := inferInstance
  exact CategoryTheory.comp_over T.toPartialMap.hom (Spec (.of k))

/-- **Hartshorne V.5, p. 410.** The graph of a rational map `T : X ⤏ Y` over `k`
on its maximal domain: the morphism `Dom(T) ⟶ X ×_k Y` whose components are the
inclusion of `Dom(T)` and the glued morphism `Dom(T) ⟶ Y`. -/
noncomputable def graphHom :
    (dom T).toScheme ⟶ pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) :=
  pullback.lift (dom T).ι (domHom T) (domHom_comp_over k T).symm

@[reassoc (attr := simp)]
theorem graphHom_fst : graphHom k T ≫ pullback.fst _ _ = (dom T).ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphHom_snd : graphHom k T ≫ pullback.snd _ _ = domHom T :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem fst_graphHom_apply (d : (dom T).toScheme) :
    pullback.fst (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (graphHom k T d) = d.1 := by
  rw [← Scheme.Hom.comp_apply, graphHom_fst, Scheme.Opens.ι_apply]

theorem snd_graphHom_apply (d : (dom T).toScheme) :
    pullback.snd (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (graphHom k T d) = domHom T d := by
  rw [← Scheme.Hom.comp_apply, graphHom_snd]

/-- **Hartshorne V.5, p. 410.** The graph `Γ_T` of `T`: the scheme-theoretic
closure in `X ×_k Y` of the graph of `T` over `Dom(T)`, i.e. the scheme-theoretic
image of the graph morphism. -/
noncomputable def graphClosure : Scheme.{u} :=
  (graphHom k T).image

/-- The closed immersion `Γ_T ⟶ X ×_k Y`. -/
noncomputable def graphClosureι :
    graphClosure k T ⟶ pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) :=
  (graphHom k T).imageι

instance : IsClosedImmersion (graphClosureι k T) :=
  inferInstanceAs (IsClosedImmersion (graphHom k T).ker.subschemeι)

theorem graphClosureι_toImage_apply (d : (dom T).toScheme) :
    graphClosureι k T ((graphHom k T).toImage d) = graphHom k T d := by
  have h : ((graphHom k T).toImage ≫ (graphHom k T).imageι) d = graphHom k T d := by
    rw [Scheme.Hom.toImage_imageι]
  exact h

/-- **Hartshorne V.5, p. 410.** The first projection `p₁ : Γ_T ⟶ X`. -/
noncomputable def graphFst : graphClosure k T ⟶ X :=
  graphClosureι k T ≫ pullback.fst _ _

/-- **Hartshorne V.5, p. 410.** The second projection `p₂ : Γ_T ⟶ Y`. -/
noncomputable def graphSnd : graphClosure k T ⟶ Y :=
  graphClosureι k T ≫ pullback.snd _ _

/-- **Hartshorne V.5, p. 410.** The total transform `T(Z) = p₂(p₁⁻¹(Z))` of a
subset `Z` of `X`. -/
def totalTransform (Z : Set X) : Set Y :=
  graphSnd k T '' (graphFst k T ⁻¹' Z)

theorem mem_totalTransform {Z : Set X} {y : Y} :
    y ∈ totalTransform k T Z ↔
      ∃ γ : graphClosure k T, graphFst k T γ ∈ Z ∧ graphSnd k T γ = y :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- Above `Dom(T)` the closure of the graph adds no points: the graph is closed in
`Dom(T) ×_k Y` because `Y` is separated. -/
theorem mem_range_graphHom_of_mem_closure
    {p : (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) : Scheme.{u})}
    (hp : p ∈ closure (Set.range (graphHom k T)))
    (hpD : pullback.fst (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) p ∈ dom T) :
    p ∈ Set.range (graphHom k T) := by
  have hYk : IsSeparated (Y ↘ Spec (.of k)) := by
    have : IsSeparated (Y ↘ Spec (.of k) ≫ terminal.from (Spec (.of k))) := by
      rw [Subsingleton.elim (Y ↘ Spec (.of k) ≫ terminal.from _) (terminal.from Y)]
      infer_instance
    exact IsSeparated.of_comp _ (terminal.from (Spec (.of k)))
  let c : (dom T).toScheme ⟶
      pullback (domHom T ≫ Y ↘ Spec (.of k)) (Y ↘ Spec (.of k)) :=
    pullback.lift (𝟙 _) (domHom T) (Category.id_comp _)
  let j := pullback.map (domHom T ≫ Y ↘ Spec (.of k)) (Y ↘ Spec (.of k))
    (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (dom T).ι (𝟙 Y) (𝟙 _)
    (by rw [Category.comp_id, domHom_comp_over]) (by simp)
  have hcj : c ≫ j = graphHom k T := by
    apply pullback.hom_ext
    · simp [c, j, pullback.map]
      exact Category.id_comp _
    · simp [c, j, pullback.map]
  have hj : Set.range j = pullback.fst (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) ⁻¹' (dom T) := by
    rw [Scheme.Pullback.range_map]
    simp
  obtain ⟨q, rfl⟩ : p ∈ Set.range j := hj ▸ hpD
  have hrange : Set.range (graphHom k T) = j '' Set.range c := by
    rw [← hcj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [hrange] at hp ⊢
  refine Set.mem_image_of_mem _ ?_
  rw [← c.isClosedEmbedding.isClosed_range.closure_eq,
    j.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
  exact hp

/-- For `X` locally Noetherian, the underlying set of `Γ_T` is the closure of the
graph. -/
theorem range_graphClosureι [IsLocallyNoetherian X] :
    Set.range (graphClosureι k T) = closure (Set.range (graphHom k T)) := by
  have : QuasiCompact (graphHom k T ≫ pullback.fst _ _) := by
    rw [graphHom_fst]
    infer_instance
  have : QuasiCompact (graphHom k T) := QuasiCompact.of_comp _ (pullback.fst _ _)
  change Set.range (graphHom k T).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

set_option backward.isDefEq.respectTransparency false in
/-- **Hartshorne V.5, p. 410.** At a point `x` where `T` is defined, the total
transform of `{x}` is the ordinary image point of `x`. -/
theorem totalTransform_singleton_of_mem_dom [IsLocallyNoetherian X] {x : X}
    (hx : x ∈ dom T) :
    totalTransform k T {x} = {domHom T ⟨x, hx⟩} := by
  ext y
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have hγ' :
        pullback.fst (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (graphClosureι k T γ) = x := hγ
    obtain ⟨d, hd⟩ := mem_range_graphHom_of_mem_closure k T
      (range_graphClosureι k T ▸ Set.mem_range_self γ) (hγ' ▸ hx)
    have hdx : d = ⟨x, hx⟩ := by
      apply Subtype.ext
      have h1 := fst_graphHom_apply k T d
      rw [hd, hγ'] at h1
      exact h1.symm
    subst hdx
    change pullback.snd (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (graphClosureι k T γ) = _
    rw [← hd, snd_graphHom_apply]
  · rintro rfl
    refine ⟨(graphHom k T).toImage ⟨x, hx⟩, ?_, ?_⟩
    · change pullback.fst (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (graphClosureι k T _) = x
      rw [graphClosureι_toImage_apply, fst_graphHom_apply]
    · change pullback.snd (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (graphClosureι k T _) = _
      rw [graphClosureι_toImage_apply, snd_graphHom_apply]

/-- The point case for `X` locally of finite type over `k`, as for a variety over
`k`: then `X` is locally Noetherian. -/
theorem totalTransform_singleton_of_mem_dom_of_locallyOfFiniteType
    [LocallyOfFiniteType (X ↘ Spec (.of k))] {x : X} (hx : x ∈ dom T) :
    totalTransform k T {x} = {domHom T ⟨x, hx⟩} :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  totalTransform_singleton_of_mem_dom k T hx

end

end SchemeRationalMap

end Hartshorne
