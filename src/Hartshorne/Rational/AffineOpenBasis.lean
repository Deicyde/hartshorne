/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.HypersurfaceComplement
import Hartshorne.Rational.OpenSubvariety
import Hartshorne.Morphism.ChartIso

/-!
# Affine opens form a basis

Hartshorne, *Algebraic Geometry*, I.4, Proposition 4.3 (p. 25).

The abstract `Variety` structure deliberately does not assert that its carrier
comes from one of Hartshorne's four concrete constructions.  Consequently the
theorem is recorded by the witness `Variety.HasAffineOpenBasis`, and proved for
concrete quasi-affine and quasi-projective varieties (hence also for affine and
projective varieties).

For a quasi-affine variety `Y = A ∩ O`, a requested neighbourhood is refined by
a principal open `D(f)`.  Its intersection with `A` is identified with the
closed graph of `1 / f`, so it is affine.  In the quasi-projective case the
result is transported through the standard-chart isomorphisms and glued over
their open cover.

## Main results

* `Hartshorne.Variety.IsAffine`
* `Hartshorne.Variety.HasAffineOpenBasis`
* `Hartshorne.Variety.hasAffineOpenBasis_ofAffine`
* `Hartshorne.Variety.hasAffineOpenBasis_ofQuasiAffine`
* `Hartshorne.Variety.hasAffineOpenBasis_ofQuasiProjective`
* `Hartshorne.Variety.hasAffineOpenBasis_ofProjective`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k]

namespace Variety

/-- A variety presented, up to isomorphism, by an affine algebraic set. -/
def IsAffine (X : Variety k) : Prop :=
  ∃ (σ : Type u) (_hσ : Finite σ) (Z : Set (σ → k)) (hZ : IsAffineVariety Z)
    (φ : VarietyHom X (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)), φ.IsIso

/-- Every neighbourhood contains an affine open neighbourhood. -/
def HasAffineOpenBasis (X : Variety k) : Prop :=
  ∀ (U : Opens X.carrier) (x : X.carrier), x ∈ U →
    ∃ (V : Opens X.carrier) (hV : (V : Set X.carrier).Nonempty),
      x ∈ V ∧ V ≤ U ∧ (X.restrict V hV).IsAffine

end Variety

namespace VarietyHom

variable {X A : Variety k}

/-- Lift a morphism whose image lies in an open set to the open subvariety. -/
noncomputable def liftToRestrict (f : VarietyHom A X) (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty) (hf : ∀ x, f x ∈ U) :
    VarietyHom A (X.restrict U hU) where
  toFun x := ⟨f x, hf x⟩
  continuous_toFun := f.continuous_toFun.subtype_mk _
  regular_comp V g hg := by
    have hreg := f.regular_comp (pushOpens U V)
      (fun w : pushOpens U V => g (ofPush w)) hg
    let F : C(A.carrier, (X.restrict U hU).carrier) :=
      ⟨fun x => ⟨f x, hf x⟩, f.continuous_toFun.subtype_mk _⟩
    change (fun x : Opens.comap F V => g ⟨F x.1, x.2⟩) ∈
      A.regular (Opens.comap F V)
    have hle : Opens.comap F V ≤
        Opens.comap ⟨f.toFun, f.continuous_toFun⟩ (pushOpens U V) := by
      intro x hx
      change f x ∈ U ∧ ∀ h : f x ∈ U,
        (⟨f x, h⟩ : (X.restrict U hU).carrier) ∈ V
      refine ⟨hf x, fun h => ?_⟩
      change F x ∈ V at hx
      have hp : (⟨f x, h⟩ : (X.restrict U hU).carrier) = F x := by
        apply Subtype.ext
        rfl
      rw [hp]
      exact hx
    have hr := A.regular_restrict hle hreg
    convert hr using 1
    funext x
    congr 2

noncomputable def ofCoords {σ : Type u} {Y : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (f : A.carrier → Y)
    (hf : ∀ i, A.IsGlobalRegular fun x => (f x).1 i) :
    VarietyHom A (Variety.ofQuasiAffine hY) :=
  Classical.choose ((exists_varietyHom_iff_coords_regular hY f).2 hf)

theorem ofCoords_toFun {σ : Type u} {Y : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (f : A.carrier → Y)
    (hf : ∀ i, A.IsGlobalRegular fun x => (f x).1 i) :
    (ofCoords hY f hf).toFun = f :=
  Classical.choose_spec ((exists_varietyHom_iff_coords_regular hY f).2 hf)

end VarietyHom

variable {σ : Type u} [Finite σ]

omit [Finite σ] in
/-- Projection forgetting the graph coordinate is Zariski-continuous. -/
theorem continuous_graphBase :
    Continuous (fun z : Option σ → k => fun i => z (some i)) := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hC
  have heq :
      (fun z : Option σ → k => fun i => z (some i)) ⁻¹' zeroSet T =
        zeroSet (rename some '' T) := by
    ext z
    simp only [Set.mem_preimage, mem_zeroSet_iff, Set.mem_image]
    constructor
    · intro hz p hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [MvPolynomial.eval_rename]
      exact hz q hq
    · intro hz q hq
      have h := hz (rename some q) ⟨q, hq, rfl⟩
      rw [MvPolynomial.eval_rename] at h
      exact h
  rw [heq]
  exact isClosed_zeroSet _

/-- The graph over a closed affine subvariety. -/
def affineGraphPiece (A : Set (σ → k)) (f : MvPolynomial σ k) :
    Set (Option σ → k) :=
  zeroLocus k (graphIdeal f) ∩
    (fun z : Option σ → k => fun i => z (some i)) ⁻¹' A

omit [Finite σ] in
theorem affineGraphPiece_isClosed {A : Set (σ → k)}
    (hA : IsAffineVariety A) (f : MvPolynomial σ k) :
    IsClosed (affineGraphPiece A f) := by
  exact (isClosed_zeroLocus _).inter (hA.isClosed.preimage continuous_graphBase)

section AlgClosed

variable [IsAlgClosed k]

noncomputable def affineGraphMap (A : Set (σ → k)) (f : MvPolynomial σ k) (hf : f ≠ 0) :
    ↑(A ∩ principalOpen f) → (Option σ → k) :=
  fun x => (graphInverseMap f hf ⟨x.1, x.2.2⟩).1

theorem continuous_affineGraphMap (A : Set (σ → k))
    (f : MvPolynomial σ k) (hf : f ≠ 0) :
    Continuous (affineGraphMap A f hf) := by
  have hincl : Continuous
      (fun x : ↑(A ∩ principalOpen f) =>
        (⟨x.1, x.2.2⟩ : ↑(principalOpen f))) :=
    continuous_subtype_val.subtype_mk _
  have hgraph : Continuous
      (fun x : ↑(principalOpen f) => (graphInverseMap f hf x).1) := by
    rw [← graphInverse_toFun]
    exact continuous_subtype_val.comp (graphInverse f hf).continuous_toFun
  exact hgraph.comp hincl

theorem affineGraphMap_image (A : Set (σ → k))
    (f : MvPolynomial σ k) (hf : f ≠ 0) :
    affineGraphMap A f hf '' Set.univ = affineGraphPiece A f := by
  ext z
  constructor
  · rintro ⟨x, -, rfl⟩
    refine ⟨(graphInverseMap f hf ⟨x.1, x.2.2⟩).2, ?_⟩
    exact x.2.1
  · intro hz
    have hzG : z ∈ zeroLocus k (graphIdeal f) := hz.1
    let zg : (GraphVariety f hf).carrier := ⟨z, hzG⟩
    let y : σ → k := fun i => z (some i)
    have hyD : y ∈ principalOpen f := (graphProjectionMap f hf zg).2
    let x : ↑(A ∩ principalOpen f) := ⟨y, hz.2, hyD⟩
    refine ⟨x, Set.mem_univ _, ?_⟩
    apply _root_.funext
    intro i
    cases i with
    | some i =>
        change x.1 i = z (some i)
        rfl
    | none =>
        have heq := hzG (graphPolynomial f)
          (Ideal.subset_span (Set.mem_singleton (graphPolynomial f)))
        simp [graphPolynomial, MvPolynomial.eval_rename] at heq
        have hmul : z none * eval (z ∘ some) f = 1 := sub_eq_zero.mp heq
        change (eval (z ∘ some) f)⁻¹ = z none
        exact inv_eq_of_mul_eq_one_left hmul

theorem affineGraphPiece_isIrreducible {A : Set (σ → k)}
    (hA : IsAffineVariety A) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hne : (A ∩ principalOpen f).Nonempty) :
    IsIrreducible (affineGraphPiece A f) := by
  have hAD : IsIrreducible (A ∩ principalOpen f) :=
    ⟨hne, IsPreirreducible.inter_isOpen hA.isIrreducible.isPreirreducible
      (principalOpen_isOpen f)⟩
  rw [← affineGraphMap_image A f hf]
  have him := (@IrreducibleSpace.isIrreducible_univ ↑(A ∩ principalOpen f) _
      (Subtype.irreducibleSpace hAD)).image
    (affineGraphMap A f hf)
    (continuous_affineGraphMap A f hf).continuousOn
  simpa only [Set.image_univ] using him

theorem affineGraphPiece_isAffine {A : Set (σ → k)}
    (hA : IsAffineVariety A) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hne : (A ∩ principalOpen f).Nonempty) :
    IsAffineVariety (affineGraphPiece A f) :=
  ⟨affineGraphPiece_isIrreducible hA f hf hne,
    affineGraphPiece_isClosed hA f⟩

omit [Finite σ] [IsAlgClosed k] in
/-- Principal opens form a basis of affine-space Zariski topology. -/
theorem exists_principalOpen_subset {O : Set (σ → k)} (hO : IsOpen O)
    {x : σ → k} (hx : x ∈ O) :
    ∃ f : MvPolynomial σ k,
      eval x f ≠ 0 ∧ principalOpen f ⊆ O := by
  obtain ⟨T, hT⟩ := isOpen_iff_isAlgebraicSet_compl.1 hO
  have hxnot : x ∉ zeroSet T := by
    rw [← hT]
    simpa only [Set.mem_compl_iff, not_not] using hx
  simp only [mem_zeroSet_iff] at hxnot
  push Not at hxnot
  obtain ⟨f, hf⟩ := hxnot
  refine ⟨f, hf.2, fun y hy => ?_⟩
  by_contra hyO
  have hyc : y ∈ Oᶜ := hyO
  rw [hT] at hyc
  exact hy (hyc f hf.1)

/-- The principal open induced on a subset of affine space. -/
def principalOpensOn (Y : Set (σ → k)) (f : MvPolynomial σ k) : Opens Y where
  carrier := Subtype.val ⁻¹' principalOpen f
  is_open' := (principalOpen_isOpen f).preimage continuous_subtype_val

omit [Finite σ] [IsAlgClosed k] in
theorem mem_principalOpensOn {Y : Set (σ → k)} {f : MvPolynomial σ k}
    {y : Y} : y ∈ principalOpensOn Y f ↔ eval y.1 f ≠ 0 :=
  Iff.rfl

noncomputable def toAffineGraphMap {Y A : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYA : Y ⊆ A) (f : MvPolynomial σ k)
    (hf : f ≠ 0) (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
  (Variety.ofQuasiAffine hY).restrict (principalOpensOn Y f) hV →
      affineGraphPiece A f :=
  fun x => ⟨(graphInverseMap f hf ⟨x.1.1, x.2⟩).1,
    (graphInverseMap f hf ⟨x.1.1, x.2⟩).2, hYA x.1.2⟩

noncomputable def fromAffineGraphMap {Y A O : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYeq : Y = A ∩ O)
    (f : MvPolynomial σ k) (hf : f ≠ 0) (hDO : principalOpen f ⊆ O)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    affineGraphPiece A f →
      ((Variety.ofQuasiAffine hY).restrict (principalOpensOn Y f) hV).carrier :=
  fun z =>
    let zg : (GraphVariety f hf).carrier := ⟨z.1, z.2.1⟩
    let y : σ → k := fun i => z.1 (some i)
    have hyD : y ∈ principalOpen f := (graphProjectionMap f hf zg).2
    have hyY : y ∈ Y := hYeq.symm ▸ ⟨z.2.2, hDO hyD⟩
    ⟨⟨y, hyY⟩, hyD⟩

def toPrincipalOpenMap {Y : Set (σ → k)} (hY : IsQuasiAffineVariety Y)
    (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    ((Variety.ofQuasiAffine hY).restrict (principalOpensOn Y f) hV).carrier →
      (PrincipalOpenVariety f hf).carrier :=
  fun x => ⟨x.1.1, x.2⟩

noncomputable def toPrincipalOpenHom {Y : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    VarietyHom ((Variety.ofQuasiAffine hY).restrict (principalOpensOn Y f) hV)
      (PrincipalOpenVariety f hf) := by
  refine VarietyHom.ofCoords (principalOpen_isQuasiAffineVariety f hf)
    (toPrincipalOpenMap hY f hf hV) ?_
  let j := (Variety.ofQuasiAffine hY).inclHom (principalOpensOn Y f) hV
  have hj : ∀ i, ((Variety.ofQuasiAffine hY).restrict
      (principalOpensOn Y f) hV).IsGlobalRegular
        (fun x => (j x).1 i) :=
    (exists_varietyHom_iff_coords_regular hY j.toFun).1 ⟨j, rfl⟩
  intro i
  convert hj i using 1
  funext x
  rfl

theorem toPrincipalOpenHom_toFun {Y : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    (toPrincipalOpenHom hY f hf hV).toFun = toPrincipalOpenMap hY f hf hV :=
  by
    unfold toPrincipalOpenHom
    apply VarietyHom.ofCoords_toFun

noncomputable def toAffineGraphHom {Y A : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYA : Y ⊆ A) (hA : IsAffineVariety A)
    (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    VarietyHom ((Variety.ofQuasiAffine hY).restrict (principalOpensOn Y f) hV)
      (Variety.ofQuasiAffine
        (affineGraphPiece_isAffine hA f hf
          ⟨hV.some.1, hYA hV.some.2, hV.some_mem⟩).isQuasiAffineVariety) := by
  let g := (graphInverse f hf).comp (toPrincipalOpenHom hY f hf hV)
  refine VarietyHom.ofCoords
    (affineGraphPiece_isAffine hA f hf
      ⟨hV.some.1, hYA hV.some.2, hV.some_mem⟩).isQuasiAffineVariety
    (toAffineGraphMap hY hYA f hf hV) ?_
  have hg : ∀ i, ((Variety.ofQuasiAffine hY).restrict
      (principalOpensOn Y f) hV).IsGlobalRegular
        (fun x => (g x).1 i) :=
    (exists_varietyHom_iff_coords_regular
      (graph_isAffineVariety f hf).isQuasiAffineVariety g.toFun).1 ⟨g, rfl⟩
  intro i
  convert hg i using 1
  funext x
  rw [VarietyHom.comp_apply, graphInverse_toFun, toPrincipalOpenHom_toFun]
  rfl

theorem toAffineGraphHom_toFun {Y A : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYA : Y ⊆ A) (hA : IsAffineVariety A)
    (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    (toAffineGraphHom hY hYA hA f hf hV).toFun =
      toAffineGraphMap hY hYA f hf hV := by
  unfold toAffineGraphHom
  apply VarietyHom.ofCoords_toFun

noncomputable def affineGraphBaseToYMap {Y A O : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYeq : Y = A ∩ O)
    (f : MvPolynomial σ k) (hf : f ≠ 0) (hDO : principalOpen f ⊆ O)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    affineGraphPiece A f → (Variety.ofQuasiAffine hY).carrier :=
  fun z => (fromAffineGraphMap hY hYeq f hf hDO hV z).1

noncomputable def affineGraphBaseToYHom {Y A O : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYA : Y ⊆ A) (hA : IsAffineVariety A)
    (hYeq : Y = A ∩ O) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hDO : principalOpen f ⊆ O)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    VarietyHom
      (Variety.ofQuasiAffine
        (affineGraphPiece_isAffine hA f hf
          ⟨hV.some.1, hYA hV.some.2, hV.some_mem⟩).isQuasiAffineVariety)
      (Variety.ofQuasiAffine hY) := by
  refine VarietyHom.ofCoords hY
    (affineGraphBaseToYMap hY hYeq f hf hDO hV) ?_
  intro i
  change IsRegularVia
    (openIota (⊤ : Opens (affineGraphPiece A f)))
    (fun z => z.1.1 (some i))
  simpa only [openIota, MvPolynomial.eval_X] using
    (isRegularVia_eval (openIota (⊤ : Opens (affineGraphPiece A f)))
      (MvPolynomial.X (some i)))

theorem affineGraphBaseToYHom_toFun {Y A O : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYA : Y ⊆ A) (hA : IsAffineVariety A)
    (hYeq : Y = A ∩ O) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hDO : principalOpen f ⊆ O)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    (affineGraphBaseToYHom hY hYA hA hYeq f hf hDO hV).toFun =
      affineGraphBaseToYMap hY hYeq f hf hDO hV := by
  unfold affineGraphBaseToYHom
  apply VarietyHom.ofCoords_toFun

noncomputable def fromAffineGraphHom {Y A O : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYA : Y ⊆ A) (hA : IsAffineVariety A)
    (hYeq : Y = A ∩ O) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hDO : principalOpen f ⊆ O)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    VarietyHom
      (Variety.ofQuasiAffine
        (affineGraphPiece_isAffine hA f hf
          ⟨hV.some.1, hYA hV.some.2, hV.some_mem⟩).isQuasiAffineVariety)
      ((Variety.ofQuasiAffine hY).restrict (principalOpensOn Y f) hV) :=
  VarietyHom.liftToRestrict
    (affineGraphBaseToYHom hY hYA hA hYeq f hf hDO hV)
    (principalOpensOn Y f) hV (fun z => by
      rw [affineGraphBaseToYHom_toFun]
      exact (fromAffineGraphMap hY hYeq f hf hDO hV z).2)

theorem fromAffineGraphHom_toFun {Y A O : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYA : Y ⊆ A) (hA : IsAffineVariety A)
    (hYeq : Y = A ∩ O) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hDO : principalOpen f ⊆ O)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    (fromAffineGraphHom hY hYA hA hYeq f hf hDO hV).toFun =
      fromAffineGraphMap hY hYeq f hf hDO hV := by
  funext z
  apply Subtype.ext
  change (affineGraphBaseToYHom hY hYA hA hYeq f hf hDO hV).toFun z = _
  rw [affineGraphBaseToYHom_toFun]
  rfl

theorem toAffineGraphHom_isIso {Y A O : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) (hYA : Y ⊆ A) (hA : IsAffineVariety A)
    (hYeq : Y = A ∩ O) (f : MvPolynomial σ k) (hf : f ≠ 0)
    (hDO : principalOpen f ⊆ O)
    (hV : (↑(principalOpensOn Y f) : Set Y).Nonempty) :
    (toAffineGraphHom hY hYA hA f hf hV).IsIso := by
  refine ⟨fromAffineGraphHom hY hYA hA hYeq f hf hDO hV, ?_, ?_⟩
  · apply VarietyHom.ext
    funext x
    rw [VarietyHom.comp_apply, fromAffineGraphHom_toFun, toAffineGraphHom_toFun]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · apply VarietyHom.ext
    funext z
    rw [VarietyHom.comp_apply, fromAffineGraphHom_toFun, toAffineGraphHom_toFun]
    apply Subtype.ext
    funext i
    cases i with
    | some i => rfl
    | none =>
        have heq := z.2.1 (graphPolynomial f)
          (Ideal.subset_span (Set.mem_singleton (graphPolynomial f)))
        simp [graphPolynomial, MvPolynomial.eval_rename] at heq
        have hmul : z.1 none * eval (z.1 ∘ some) f = 1 := sub_eq_zero.mp heq
        change (eval (z.1 ∘ some) f)⁻¹ = z.1 none
        exact inv_eq_of_mul_eq_one_left hmul

/-- The affine-open-basis property for a concrete quasi-affine variety. -/
theorem Variety.hasAffineOpenBasis_ofQuasiAffine {Y : Set (σ → k)}
    (hY : IsQuasiAffineVariety Y) :
    (Variety.ofQuasiAffine hY).HasAffineOpenBasis := by
  intro U x hxU
  have hYcopy := hY
  obtain ⟨-, A, O₀, hA, hO₀, hYeq⟩ := hYcopy
  have hYA : Y ⊆ A := by
    rw [hYeq]
    exact Set.inter_subset_left
  have hxO₀ : x.1 ∈ O₀ := by
    have hx : x.1 ∈ A ∩ O₀ := by
      rw [← hYeq]
      exact x.2
    exact hx.2
  have hUopen := U.isOpen
  have hxUcopy := hxU
  unfold Variety.ofQuasiAffine at hUopen
  rw [isOpen_induced_iff] at hUopen
  obtain ⟨O₁, hO₁, hUeq⟩ := hUopen
  have hxO₁ : x.1 ∈ O₁ := by
    exact (Set.ext_iff.mp hUeq x).mpr hxUcopy
  obtain ⟨f, hfx, hfsub⟩ :=
    exists_principalOpen_subset (hO₀.inter hO₁) ⟨hxO₀, hxO₁⟩
  have hf : f ≠ 0 := by
    intro h
    subst f
    simp at hfx
  let V : Opens (Variety.ofQuasiAffine hY).carrier := principalOpensOn Y f
  have hV : (V : Set (Variety.ofQuasiAffine hY).carrier).Nonempty := ⟨x, hfx⟩
  refine ⟨V, hV, hfx, ?_, ?_⟩
  · intro y hy
    exact (Set.ext_iff.mp hUeq y).mp (hfsub hy).2
  · have hDO₀ : principalOpen f ⊆ O₀ := fun y hy => (hfsub hy).1
    have hAD : (A ∩ principalOpen f).Nonempty := ⟨x.1, hYA x.2, hfx⟩
    have hZ := affineGraphPiece_isAffine hA f hf hAD
    refine ⟨Option σ, inferInstance, affineGraphPiece A f, hZ,
      toAffineGraphHom hY hYA hA f hf hV, ?_⟩
    exact toAffineGraphHom_isIso hY hYA hA hYeq f hf hDO₀ hV

/-- The affine case of Proposition 4.3. -/
theorem Variety.hasAffineOpenBasis_ofAffine {Y : Set (σ → k)}
    (hY : IsAffineVariety Y) :
    (Variety.ofQuasiAffine hY.isQuasiAffineVariety).HasAffineOpenBasis :=
  Variety.hasAffineOpenBasis_ofQuasiAffine hY.isQuasiAffineVariety

end AlgClosed

namespace Variety

theorem IsAffine.of_isIso {X Y : Variety k} (hY : Y.IsAffine)
    {f : VarietyHom X Y} (hf : f.IsIso) : X.IsAffine := by
  obtain ⟨τ, hτ, Z, hZ, g, hg⟩ := hY
  exact ⟨τ, hτ, Z, hZ, g.comp f, hg.comp hf⟩

@[simp]
theorem inclHom_apply {X : Variety k} (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty) (x : (X.restrict U hU).carrier) :
    X.inclHom U hU x = x.1 := rfl

noncomputable def isoPreimageOpen {X Y : Variety k}
    (f : VarietyHom X Y) (V : Opens Y.carrier) : Opens X.carrier :=
  Opens.comap ⟨f.toFun, f.continuous_toFun⟩ V

noncomputable def restrictIsoPreimageHom {X Y : Variety k}
    (f : VarietyHom X Y) (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty)
    (hP : ((isoPreimageOpen f V : Opens X.carrier) : Set X.carrier).Nonempty) :
    VarietyHom (X.restrict (isoPreimageOpen f V) hP) (Y.restrict V hV) :=
  VarietyHom.liftToRestrict
    (f.comp (X.inclHom (isoPreimageOpen f V) hP)) V hV (fun x => x.2)

theorem restrictIsoPreimageHom_isIso {X Y : Variety k}
    {f : VarietyHom X Y} (hf : f.IsIso) (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty)
    (hP : ((isoPreimageOpen f V : Opens X.carrier) : Set X.carrier).Nonempty) :
    (restrictIsoPreimageHom f V hV hP).IsIso := by
  obtain ⟨g, hgf, hfg⟩ := hf
  let gV : VarietyHom (Y.restrict V hV) X := g.comp (Y.inclHom V hV)
  have hgV (y : (Y.restrict V hV).carrier) : gV y ∈ isoPreimageOpen f V := by
    change f (g y.1) ∈ V
    have he := congrArg (fun q : VarietyHom Y Y => q y.1) hfg
    simpa using he.symm ▸ y.2
  let gR : VarietyHom (Y.restrict V hV)
      (X.restrict (isoPreimageOpen f V) hP) :=
    VarietyHom.liftToRestrict gV (isoPreimageOpen f V) hP hgV
  refine ⟨gR, ?_, ?_⟩
  · apply VarietyHom.ext
    funext x
    apply Subtype.ext
    have he := congrArg (fun q : VarietyHom X X => q x.1) hgf
    simpa [gR, gV, restrictIsoPreimageHom, VarietyHom.liftToRestrict] using he
  · apply VarietyHom.ext
    funext y
    apply Subtype.ext
    have he := congrArg (fun q : VarietyHom Y Y => q y.1) hfg
    simpa [gR, gV, restrictIsoPreimageHom, VarietyHom.liftToRestrict] using he

theorem HasAffineOpenBasis.of_isIso {X Y : Variety k}
    (hY : Y.HasAffineOpenBasis) {f : VarietyHom X Y} (hf : f.IsIso) :
    X.HasAffineOpenBasis := by
  have hf0 := hf
  obtain ⟨g, hgf, hfg⟩ := hf
  intro U x hx
  let U' := isoPreimageOpen g U
  have hfx : f x ∈ U' := by
    change g (f x) ∈ U
    have he := congrArg (fun q : VarietyHom X X => q x) hgf
    simpa using he.symm ▸ hx
  obtain ⟨V, hV, hfxV, hVU, hVaff⟩ := hY U' (f x) hfx
  let P := isoPreimageOpen f V
  have hP : ((P : Opens X.carrier) : Set X.carrier).Nonempty := ⟨x, hfxV⟩
  refine ⟨P, hP, hfxV, ?_, ?_⟩
  · intro y hy
    have hfgU : g (f y) ∈ U := hVU hy
    have he := congrArg (fun q : VarietyHom X X => q y) hgf
    have he' : g (f y) = y := by simpa using he
    rw [he'] at hfgU
    exact hfgU
  · exact IsAffine.of_isIso hVaff
      (restrictIsoPreimageHom_isIso hf0 V hV hP)

theorem pushOpens_nonempty {X : Variety k} {U : Opens X.carrier}
    {hU : (U : Set X.carrier).Nonempty}
    {V : Opens (X.restrict U hU).carrier}
    (hV : (V : Set (X.restrict U hU).carrier).Nonempty) :
    ((pushOpens U V : Opens X.carrier) : Set X.carrier).Nonempty := by
  obtain ⟨v, hv⟩ := hV
  exact ⟨v.1, v.2, fun _ => hv⟩

noncomputable def flattenRestrictHom {X : Variety k}
    (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty)
    (V : Opens (X.restrict U hU).carrier)
    (hV : (V : Set (X.restrict U hU).carrier).Nonempty) :
    VarietyHom ((X.restrict U hU).restrict V hV)
      (X.restrict (pushOpens U V) (pushOpens_nonempty hV)) := by
  let toX : VarietyHom ((X.restrict U hU).restrict V hV) X :=
    (X.inclHom U hU).comp ((X.restrict U hU).inclHom V hV)
  apply VarietyHom.liftToRestrict toX (pushOpens U V) (pushOpens_nonempty hV)
  intro x
  exact ⟨x.1.2, fun _ => x.2⟩

noncomputable def unflattenRestrictHom {X : Variety k}
    (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty)
    (V : Opens (X.restrict U hU).carrier)
    (hV : (V : Set (X.restrict U hU).carrier).Nonempty) :
    VarietyHom (X.restrict (pushOpens U V) (pushOpens_nonempty hV))
      ((X.restrict U hU).restrict V hV) := by
  let toX : VarietyHom (X.restrict (pushOpens U V) (pushOpens_nonempty hV)) X :=
    X.inclHom (pushOpens U V) (pushOpens_nonempty hV)
  let toU : VarietyHom (X.restrict (pushOpens U V) (pushOpens_nonempty hV))
      (X.restrict U hU) :=
    VarietyHom.liftToRestrict toX U hU (fun x => x.2.1)
  apply VarietyHom.liftToRestrict toU V hV
  intro x
  exact x.2.2 x.2.1

theorem unflattenRestrictHom_isIso {X : Variety k}
    (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty)
    (V : Opens (X.restrict U hU).carrier)
    (hV : (V : Set (X.restrict U hU).carrier).Nonempty) :
    (unflattenRestrictHom U hU V hV).IsIso := by
  refine ⟨flattenRestrictHom U hU V hV, ?_, ?_⟩
  · apply VarietyHom.ext
    funext x
    rfl
  · apply VarietyHom.ext
    funext x
    rfl

theorem HasAffineOpenBasis.of_open_cover {X : Variety k}
    (hcover : ∀ x : X.carrier, ∃ (U : Opens X.carrier)
      (hU : (U : Set X.carrier).Nonempty),
      x ∈ U ∧ (X.restrict U hU).HasAffineOpenBasis) :
    X.HasAffineOpenBasis := by
  intro O x hxO
  obtain ⟨U, hU, hxU, hUbasis⟩ := hcover x
  let O' : Opens (X.restrict U hU).carrier :=
    Opens.comap ⟨(X.inclHom U hU).toFun, (X.inclHom U hU).continuous_toFun⟩ O
  have hxO' : (⟨x, hxU⟩ : (X.restrict U hU).carrier) ∈ O' := hxO
  obtain ⟨V, hV, hxV, hVO, hVaff⟩ := hUbasis O' ⟨x, hxU⟩ hxO'
  let W := pushOpens U V
  have hW : ((W : Opens X.carrier) : Set X.carrier).Nonempty :=
    pushOpens_nonempty hV
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · exact ⟨hxU, fun _ => hxV⟩
  · intro y hy
    exact hVO (hy.2 hy.1)
  · exact IsAffine.of_isIso hVaff (unflattenRestrictHom_isIso U hU V hV)

end Variety

section Projective

variable [IsAlgClosed k] { τ : Type u } [Finite τ] [DecidableEq τ]
  [Nonempty τ] {Y : Set (ProjectiveSpace k τ)}

omit [IsAlgClosed k] [Finite τ] [DecidableEq τ] [Nonempty τ] in
noncomputable def projectiveChartOpen (hY : IsQuasiProjVariety Y) (i : τ) :
    Opens (Variety.ofQuasiProjective hY).carrier where
  carrier := {y : Y | y.1 ∈ Y ∩ standardChart i}
  is_open' := by
    change IsOpen {y : Y | y.1 ∈ Y ∩ standardChart i}
    exact isOpen_inter_standardChart_in (k := k) i

omit [IsAlgClosed k] [Finite τ] [DecidableEq τ] [Nonempty τ] in
theorem projectiveChartOpen_nonempty (hY : IsQuasiProjVariety Y) (i : τ)
    (hne : (Y ∩ standardChart i).Nonempty) :
    ((projectiveChartOpen hY i : Opens (Variety.ofQuasiProjective hY).carrier) :
      Set (Variety.ofQuasiProjective hY).carrier).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  exact ⟨⟨p, hp.1⟩, hp⟩

noncomputable def restrictChartToChartVariety (hY : IsQuasiProjVariety Y)
    (i : τ) (hne : (Y ∩ standardChart i).Nonempty) :
    VarietyHom
      ((Variety.ofQuasiProjective hY).restrict
        (projectiveChartOpen hY i)
        (projectiveChartOpen_nonempty hY i hne))
      (chartVariety k i hY hne) where
  toFun p := ⟨p.1.1, p.1.2, p.2.2⟩
  continuous_toFun := by
    change Continuous (fun p : projectiveChartOpen hY i =>
      (⟨p.1.1, p.1.2, p.2.2⟩ : ↥(Y ∩ standardChart i)))
    exact (continuous_subtype_val.comp
      (Variety.inclHom (Variety.ofQuasiProjective hY) (projectiveChartOpen hY i)
        (projectiveChartOpen_nonempty hY i hne)).continuous_toFun).subtype_mk _
  regular_comp V f hf := by
    rw [Variety.mem_restrict_regular]
    let qV :
        (pushOpens (projectiveChartOpen hY i)
          (Opens.comap
            ⟨fun p => (⟨p.1.1, p.1.2, p.2.2⟩ : ↥(Y ∩ standardChart i)), by
              exact (continuous_subtype_val.comp
                (Variety.inclHom (Variety.ofQuasiProjective hY) (projectiveChartOpen hY i)
                  (projectiveChartOpen_nonempty hY i hne)).continuous_toFun).subtype_mk _⟩ V)) → V :=
      fun x => ⟨⟨x.1.1, x.1.2, x.2.1.2⟩, x.2.2 x.2.1⟩
    have hqV : Continuous qV := by
      dsimp [qV]
      fun_prop
    intro P
    obtain ⟨W, hW, hPW, n, g, h, hg, hh, hne', he⟩ :=
      (mem_projRegularSubalgebra.1 hf) (qV P)
    refine ⟨qV ⁻¹' W, hW.preimage hqV, hPW, n, g, h, hg, hh, ?_, ?_⟩
    · intro x hx
      exact hne' (qV x) hx
    · intro x hx
      exact he (qV x) hx

noncomputable def chartVarietyToRestrictChart (hY : IsQuasiProjVariety Y)
    (i : τ) (hne : (Y ∩ standardChart i).Nonempty) :
    VarietyHom (chartVariety k i hY hne)
      ((Variety.ofQuasiProjective hY).restrict
        (projectiveChartOpen hY i)
        (projectiveChartOpen_nonempty hY i hne)) where
  toFun p := ⟨⟨p.1, p.2.1⟩, p.2⟩
  continuous_toFun := by
    change Continuous (fun p : ↥(Y ∩ standardChart i) =>
      (⟨⟨p.1, p.2.1⟩, p.2⟩ : projectiveChartOpen hY i))
    fun_prop
  regular_comp V f hf := by
    have hf' := (Variety.mem_restrict_regular).1 hf
    change IsRegularProjVia _ _
    let rV :
        (Opens.comap
          ⟨fun p : ↥(Y ∩ standardChart i) =>
              (⟨⟨p.1, p.2.1⟩, p.2⟩ : projectiveChartOpen hY i), by
            fun_prop⟩ V) → pushOpens (projectiveChartOpen hY i) V :=
      fun x => toPush ⟨⟨⟨x.1.1, x.1.2.1⟩, x.1.2⟩, x.2⟩
    have hrV : Continuous rV := by
      dsimp [rV, toPush]
      fun_prop
    intro P
    obtain ⟨W, hW, hPW, n, g, h, hg, hh, hne', he⟩ :=
      (mem_projRegularSubalgebra.1 hf') (rV P)
    refine ⟨rV ⁻¹' W, hW.preimage hrV, hPW, n, g, h, hg, hh, ?_, ?_⟩
    · intro x hx
      exact hne' (rV x) hx
    · intro x hx
      exact he (rV x) hx

omit [IsAlgClosed k] [Finite τ] [DecidableEq τ] [Nonempty τ] in
theorem isIso_restrictChartToChartVariety (hY : IsQuasiProjVariety Y)
    (i : τ) (hne : (Y ∩ standardChart i).Nonempty) :
    (restrictChartToChartVariety hY i hne).IsIso := by
  refine ⟨chartVarietyToRestrictChart hY i hne, ?_, ?_⟩
  · apply VarietyHom.ext
    funext p
    rfl
  · apply VarietyHom.ext
    funext p
    rfl

noncomputable def restrictChartHom (hY : IsQuasiProjVariety Y)
    (i : τ) (hne : (Y ∩ standardChart i).Nonempty) :
    VarietyHom
      ((Variety.ofQuasiProjective hY).restrict
        (projectiveChartOpen hY i)
        (projectiveChartOpen_nonempty hY i hne))
      (chartTarget k i hY hne) :=
  (chartHom k i hY hne).comp (restrictChartToChartVariety hY i hne)

theorem isIso_restrictChartHom (hY : IsQuasiProjVariety Y)
    (i : τ) (hne : (Y ∩ standardChart i).Nonempty) :
    (restrictChartHom hY i hne).IsIso :=
  (isIso_chartHom k i hY hne).comp
    (isIso_restrictChartToChartVariety hY i hne)

theorem Variety.hasAffineOpenBasis_ofQuasiProjective
    (hY : IsQuasiProjVariety Y) :
    (Variety.ofQuasiProjective hY).HasAffineOpenBasis := by
  apply Variety.HasAffineOpenBasis.of_open_cover
  intro x
  obtain ⟨i, hi⟩ := exists_mem_standardChart x.1
  let hne : (Y ∩ standardChart i).Nonempty := ⟨x.1, x.2, hi⟩
  let C := projectiveChartOpen hY i
  let hC : ((C : Opens (Variety.ofQuasiProjective hY).carrier) :
      Set (Variety.ofQuasiProjective hY).carrier).Nonempty :=
    projectiveChartOpen_nonempty hY i hne
  have hxC : x ∈ C := ⟨x.2, hi⟩
  refine ⟨C, hC, hxC, ?_⟩
  have htarget : (chartTarget k i hY hne).HasAffineOpenBasis :=
    Variety.hasAffineOpenBasis_ofQuasiAffine
      (isQuasiAffineVariety_chartMap_image i hY hne)
  exact Variety.HasAffineOpenBasis.of_isIso htarget
    (isIso_restrictChartHom hY i hne)

theorem Variety.hasAffineOpenBasis_ofProjective (hY : IsProjVariety Y) :
    (Variety.ofProjective hY).HasAffineOpenBasis :=
  Variety.hasAffineOpenBasis_ofQuasiProjective hY.isQuasiProjVariety

end Projective

end Hartshorne
