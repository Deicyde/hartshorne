/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.FlatFamilies.FlatFibreLocalDimension
import Hartshorne.Dimension.FgDomain
import Hartshorne.Dimension.HeightCoheight
import Hartshorne.Scheme.DimensionCodimension
import Hartshorne.Scheme.ReducedInducedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Equidimensionality in a flat family

Hartshorne, *Algebraic Geometry*, III.9, Corollary 9.6 (p. 257).

Let `f : X → Y` be a flat morphism of schemes of finite type over a field `k`, with `Y`
irreducible. Every irreducible component of `X` has dimension `dim Y + n` if and only if, for
every point `y ∈ Y`, every irreducible component of the scheme-theoretic fibre `X_y` has
dimension `n`. Here the dimension of an irreducible component is its dimension as a topological
subspace, and `n` is a natural number.

## Strategy

We work in the specialization order on the points of a scheme (`x ≤ z` when `z` is a
generalization of `x`). For a point `x`, `height x` is the dimension of `cl{x}` and
`coheight x` is `dim 𝒪_{X,x}` (Mathlib's `ringKrullDim_stalk_eq_coheight`); the dimension of an
irreducible component with generic point `ζ` is `height ζ`.

* `catenaryAt_of_finiteType`: on a scheme of finite type over a field, for `x ≤ g` the height of
  `x` plus the length of the longest chain from `x` up to `g` is `height g`, a natural number.
  This is the height-plus-coheight formula of the dimension–codimension article applied to the
  reduced induced (integral) closed subscheme on `cl{g}`.
* From this, a closed point lying on a single irreducible component `Z` has local dimension
  `dim Z`, and if every component has dimension `D` then `dim 𝒪_{X,x} + dim cl{x} = D` for all
  `x`.
* `height_eq_height_of_forall`: if `x` is closed in its fibre then `dim cl{x} = dim cl{f x}`.
  On affine charts `Spec B → Spec A` this says `dim B/q = dim A/p` for `p = q ∩ A`, which holds
  because both are transcendence degrees over `k` and `κ(q)` is algebraic over `κ(p)`: `q`
  corresponds to a maximal ideal of the fibre ring `κ(p) ⊗_A B`, a finitely generated
  `κ(p)`-algebra, so Zariski's lemma applies.
* The corollary follows from Proposition 9.5 (`dim 𝒪_{X_y,x} + dim 𝒪_{Y,y} = dim 𝒪_{X,x}`)
  applied at a closed point of the fibre (respectively of `X`) lying on a single irreducible
  component.

## Main result

* `Hartshorne.forall_irreducibleComponents_topologicalKrullDim_eq_add_iff`
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Order

namespace Hartshorne

universe u

namespace FlatEquidimensional

section Poset

variable {α : Type*} [Preorder α]

/-- The catenary condition at `g`: `height g` is a natural number `N`, and every `x ≤ g`
satisfies `height x + coheight x = N`, the coheight being computed inside `Set.Iic g`. -/
def CatenaryAt (g : α) : Prop :=
  ∃ N : ℕ, height g = N ∧ ∀ x (hx : x ≤ g), height x + coheight (⟨x, hx⟩ : Set.Iic g) = N

/-- Heights in `Set.Iic g` agree with heights in the ambient order. -/
theorem height_Iic_coe {g : α} (x : Set.Iic g) : height x = height (x : α) :=
  height_eq_of_strictMono Subtype.val (fun _ _ h => h)
    (fun a b hb => ⟨⟨b, hb.le.trans a.2⟩, hb, rfl⟩) x

/-- A chain starting at `x` and ending below `g` bounds the coheight of `x` inside
`Set.Iic g`. -/
theorem length_le_coheight_Iic {g x : α} (p : LTSeries α) (hp : p.head = x)
    (hg : p.last ≤ g) (hx : x ≤ g) : (p.length : ℕ∞) ≤ coheight (⟨x, hx⟩ : Set.Iic g) := by
  subst hp
  let q : LTSeries (Set.Iic g) :=
    ⟨p.length, fun i => ⟨p i, (p.monotone (Fin.le_last i)).trans hg⟩, fun i => p.step i⟩
  exact length_le_coheight_head (p := q)

/-- If every element above `x` lies below `g`, the coheight of `x` may be computed inside
`Set.Iic g`. -/
theorem coheight_Iic_coe_of_forall {g x : α} (hx : x ≤ g) (hup : ∀ z, x ≤ z → z ≤ g) :
    coheight (⟨x, hx⟩ : Set.Iic g) = coheight x := by
  refine le_antisymm (coheight_le_coheight_apply_of_strictMono Subtype.val (fun _ _ h => h) _) ?_
  refine coheight_le fun p hp => ?_
  have hlast : p.last ≤ g := hup _ (hp ▸ p.monotone (Fin.zero_le _))
  exact length_le_coheight_Iic p hp hlast hx

/-- If every element above `x` lies below `g`, and the order is catenary at `g`, then
`coheight x + height x = height g`. -/
theorem coheight_add_height_eq_of_forall {g x : α} (hC : CatenaryAt g) (hx : x ≤ g)
    (hup : ∀ z, x ≤ z → z ≤ g) : coheight x + height x = height g := by
  obtain ⟨N, hN, h⟩ := hC
  rw [hN, ← h x hx, coheight_Iic_coe_of_forall hx hup, add_comm]

/-- In a catenary order in which every element lies below an element of height `D`,
every element satisfies `coheight x + height x = D`. -/
theorem coheight_add_height_eq_of_equidim (hC : ∀ g : α, CatenaryAt g) {D : ℕ}
    (hD : ∀ z : α, ∃ g, z ≤ g ∧ height g = D) (x : α) :
    coheight x + height x = D := by
  obtain ⟨g, hxg, hg⟩ := hD x
  obtain ⟨N, hN, h⟩ := hC g
  have hND : N = D := by exact_mod_cast hN.symm.trans hg
  subst hND
  have hx := h x hxg
  obtain ⟨m, hm⟩ : ∃ m : ℕ, height x = m :=
    ENat.ne_top_iff_exists.mp (fun ht => by simp [ht] at hx) |>.imp fun _ e => e.symm
  have hmN : m ≤ N := by
    have : (m : ℕ∞) ≤ N := hm ▸ hx ▸ le_self_add
    exact_mod_cast this
  rw [hm]
  refine le_antisymm ?_ ?_
  · have : coheight x ≤ ((N - m : ℕ) : ℕ∞) := by
      refine coheight_le fun p hp => ?_
      obtain ⟨g', hg', hg'D⟩ := hD p.last
      obtain ⟨N', hN', h'⟩ := hC p.last
      have hxl : x ≤ p.last := hp ▸ p.monotone (Fin.zero_le _)
      have hlen := length_le_coheight_Iic p hp le_rfl hxl
      have hx' := h' x hxl
      have hN'N : (N' : ℕ∞) ≤ N := by
        rw [← hN', ← hg'D]; exact height_mono hg'
      rw [hm] at hx'
      obtain ⟨c, hc⟩ : ∃ c : ℕ, coheight (⟨x, hxl⟩ : Set.Iic p.last) = c :=
        ENat.ne_top_iff_exists.mp (fun ht => by simp [ht] at hx') |>.imp fun _ e => e.symm
      rw [hc] at hx' hlen
      have h1 : m + c = N' := by exact_mod_cast hx'
      have h2 : N' ≤ N := by exact_mod_cast hN'N
      have h3 : p.length ≤ c := by exact_mod_cast hlen
      exact_mod_cast (show p.length ≤ N - m by omega)
    calc coheight x + m ≤ ((N - m : ℕ) : ℕ∞) + m := by gcongr
      _ = N := by norm_cast; omega
  · rw [← hx, hm, add_comm]
    gcongr
    exact coheight_le_coheight_apply_of_strictMono Subtype.val (fun _ _ h => h) _

end Poset

section Scheme

/-- The dimension of the closure of a point is the height of the point in the specialization
order. -/
theorem topologicalKrullDim_closure_singleton {S : Scheme.{u}} (g : S) :
    topologicalKrullDim (closure ({g} : Set S)) = (height g : WithBot ℕ∞) := by
  rw [topologicalKrullDim_subtype_eq isClosed_closure]
  let e : IrreducibleCloseds S ≃o S := irreducibleSetEquivPoints
  let Z₀ : IrreducibleCloseds S := e.symm g
  change Order.krullDim (Set.Iic Z₀) = _
  rw [← height_eq_krullDim_Iic, ← height_orderIso e.symm g]

/-- A scheme of finite type over a field is catenary at every point, in the sense of
`CatenaryAt`. This is the height-plus-coheight formula for the reduced induced closed
subscheme on `cl{g}`, which is integral of finite type over the field. -/
theorem catenaryAt_of_finiteType {K : Type u} [Field K] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of K)) (hs : FiniteType s) (g : S) : CatenaryAt g := by
  let Zc : Closeds S := ⟨closure {g}, isClosed_closure⟩
  let W := reducedInducedSubscheme Zc
  let ι : W ⟶ S := reducedInducedSubschemeι Zc
  have hrange : Set.range ι = closure {g} := range_reducedInducedSubschemeι Zc
  have hemb : IsClosedEmbedding ι := ι.isClosedEmbedding
  have hle : ∀ a b : W, ι a ≤ ι b ↔ a ≤ b := fun a b => hemb.isInducing.specializes_iff
  have hmem : ∀ z : S, z ∈ Set.range ι ↔ z ≤ g := fun z => by
    rw [hrange]; exact specializes_iff_mem_closure.symm
  have : IrreducibleSpace (Set.range ι) := by
    rw [hrange]; exact Subtype.irreducibleSpace isIrreducible_singleton.closure
  have : IrreducibleSpace W :=
    (hemb.isEmbedding.toHomeomorph).symm.surjective.irreducibleSpace
      (hemb.isEmbedding.toHomeomorph).symm.continuous
  have : IsIntegral W := isIntegral_of_irreducibleSpace_of_isReduced W
  have hft : FiniteType (ι ≫ s) := by
    have := hs.1; have := hs.2
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨w₀⟩ : Nonempty W := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hwU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show w₀ ∈ (⊤ : W.Opens) from trivial)
      isOpen_univ
  have : Nonempty U := ⟨⟨w₀, hwU⟩⟩
  obtain ⟨N, -, hN⟩ := DimensionCodimension.exists_ringKrullDim_eq (ι ≫ s) hft U hU
  let e : IrreducibleCloseds W ≃o W := irreducibleSetEquivPoints
  have key : ∀ w : W, height w + coheight w = N := fun w => by
    have h := DimensionCodimension.height_add_coheight (ι ≫ s) hft (e.symm w)
    rw [hN, height_orderIso, coheight_orderIso] at h
    exact_mod_cast h
  let Φ : W ≃o Set.Iic g :=
    { Equiv.ofBijective (fun w => (⟨ι w, (hmem _).mp ⟨w, rfl⟩⟩ : Set.Iic g))
        ⟨fun a b h => hemb.injective (Subtype.mk.inj h),
          fun z => (hmem z.1).mpr z.2 |>.imp fun w hw => Subtype.ext hw⟩ with
      map_rel_iff' := fun {a b} => hle a b }
  have hfor : ∀ x (hx : x ≤ g), height x + coheight (⟨x, hx⟩ : Set.Iic g) = N := by
    intro x hx
    have h1 := key (Φ.symm ⟨x, hx⟩)
    rw [← height_orderIso Φ, ← coheight_orderIso Φ, Φ.apply_symm_apply, height_Iic_coe] at h1
    exact h1
  refine ⟨N, ?_, hfor⟩
  have h := hfor g (le_refl g)
  have h0 : coheight (⟨g, le_refl g⟩ : Set.Iic g) = 0 := coheight_eq_zero.mpr fun y _ => y.2
  rwa [h0, add_zero] at h

end Scheme

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- If the prime `q` of `B` is maximal among the primes with the same contraction `p` to `A`,
then the corresponding prime of the fibre ring `κ(p) ⊗_A B` is maximal. -/
theorem isMaximal_fiber (q : Ideal B) [q.IsPrime]
    (hq : ∀ q' : Ideal B, q'.IsPrime → q ≤ q' →
      q'.comap (algebraMap A B) = q.comap (algebraMap A B) → q' = q) :
    (PrimeSpectrum.preimageOrderIsoFiber A B
      (PrimeSpectrum.comap (algebraMap A B) ⟨q, inferInstance⟩)
      ⟨⟨q, inferInstance⟩, rfl⟩).asIdeal.IsMaximal := by
  set P := PrimeSpectrum.comap (algebraMap A B) ⟨q, inferInstance⟩
  set e := PrimeSpectrum.preimageOrderIsoFiber A B P
  set q₀ : PrimeSpectrum.comap (algebraMap A B) ⁻¹' {P} := ⟨⟨q, inferInstance⟩, rfl⟩
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal (e q₀).asIdeal (e q₀).isPrime.ne_top
  suffices h : e.symm ⟨M, hM.isPrime⟩ = q₀ by
    have : (⟨M, hM.isPrime⟩ : PrimeSpectrum _) = e q₀ := by rw [← h, e.apply_symm_apply]
    rw [← this]; exact hM
  have hle : q₀ ≤ e.symm ⟨M, hM.isPrime⟩ := by
    have := e.symm.monotone (show e q₀ ≤ ⟨M, hM.isPrime⟩ from hQM)
    rwa [e.symm_apply_apply] at this
  have hmem := (e.symm ⟨M, hM.isPrime⟩).2
  apply Subtype.ext
  apply PrimeSpectrum.ext
  refine hq _ inferInstance hle ?_
  have := congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hmem)
  simpa [P] using this

/-- If `q` is maximal among the primes of `B` over `p = q ∩ A` and `B` is a finitely generated
`A`-algebra, then the image of every element of `B` in `κ(q)` is integral over `κ(p)`
(Zariski's lemma for the fibre ring `κ(p) ⊗_A B`). -/
theorem isIntegral_algebraMap_residueField [Algebra.FiniteType A B] (q : Ideal B) [q.IsPrime]
    (hq : ∀ q' : Ideal B, q'.IsPrime → q ≤ q' →
      q'.comap (algebraMap A B) = q.comap (algebraMap A B) → q' = q) (b : B) :
    letI := (Ideal.ResidueField.map (q.comap (algebraMap A B)) q (algebraMap A B) rfl).toAlgebra
    IsIntegral (q.comap (algebraMap A B)).ResidueField (algebraMap B q.ResidueField b) := by
  set P := PrimeSpectrum.comap (algebraMap A B) ⟨q, inferInstance⟩
  let := (Ideal.ResidueField.map P.asIdeal q (algebraMap A B) rfl).toAlgebra
  show IsIntegral P.asIdeal.ResidueField _
  set e := PrimeSpectrum.preimageOrderIsoFiber A B P
  set q₀ : PrimeSpectrum.comap (algebraMap A B) ⁻¹' {P} := ⟨⟨q, inferInstance⟩, rfl⟩
  set Q := e q₀
  have hQ : Q.asIdeal.IsMaximal := isMaximal_fiber q hq
  let : Field (P.asIdeal.Fiber B ⧸ Q.asIdeal) := Ideal.Quotient.field _
  have : Module.Finite P.asIdeal.ResidueField (P.asIdeal.Fiber B ⧸ Q.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  let L := Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ P.asIdeal q (Algebra.ofId _ _) (by rfl))
      (IsScalarTower.toAlgHom A B q.ResidueField) fun _ _ ↦ .all _ _
  have hker : ∀ a ∈ Q.asIdeal, L a = 0 := fun a ha => ha
  let ψ : P.asIdeal.Fiber B ⧸ Q.asIdeal →+* q.ResidueField :=
    Ideal.Quotient.lift Q.asIdeal L.toRingHom hker
  have hψ : (algebraMap P.asIdeal.ResidueField q.ResidueField).comp (RingHom.id _) =
      ψ.comp (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber B ⧸ Q.asIdeal)) := by
    refine RingHom.ext fun c => ?_
    change _ = L (algebraMap _ (P.asIdeal.Fiber B) c)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, map_one, mul_one,
      RingHom.comp_apply]
    rfl
  have hint : IsIntegral P.asIdeal.ResidueField
      (Ideal.Quotient.mk Q.asIdeal ((1 : P.asIdeal.ResidueField) ⊗ₜ[A] b)) :=
    Algebra.IsIntegral.isIntegral _
  have := hint.map_of_comp_eq (RingHom.id _) ψ hψ
  have h2 : ψ (Ideal.Quotient.mk Q.asIdeal ((1 : P.asIdeal.ResidueField) ⊗ₜ[A] b)) =
      algebraMap B q.ResidueField b := by
    simp [ψ, L]
  rw [h2] at this
  exact this

/-- If `q` is maximal among the primes of `B` over `p = q ∩ A` and `B` is a finitely generated
`A`-algebra, then `κ(q)` is algebraic over `κ(p)`. -/
theorem isAlgebraic_residueField [Algebra.FiniteType A B] (q : Ideal B) [q.IsPrime]
    (hq : ∀ q' : Ideal B, q'.IsPrime → q ≤ q' →
      q'.comap (algebraMap A B) = q.comap (algebraMap A B) → q' = q) :
    letI := (Ideal.ResidueField.map (q.comap (algebraMap A B)) q (algebraMap A B) rfl).toAlgebra
    Algebra.IsAlgebraic (q.comap (algebraMap A B)).ResidueField q.ResidueField := by
  let := (Ideal.ResidueField.map (q.comap (algebraMap A B)) q (algebraMap A B) rfl).toAlgebra
  refine ⟨fun x => ?_⟩
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ q) x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  simp only [Ideal.algebraMap_quotient_residueField_mk]
  rw [div_eq_mul_inv]
  refine (IsIntegral.mul (isIntegral_algebraMap_residueField q hq a) ?_).isAlgebraic
  rw [← isAlgebraic_iff_isIntegral, IsAlgebraic.inv_iff, isAlgebraic_iff_isIntegral]
  exact isIntegral_algebraMap_residueField q hq s

/-- Let `A → B` be a map of finitely generated `k`-algebras and `q` a prime of `B` that is
maximal among the primes of `B` with the same contraction `p` to `A`. Then
`dim B/q = dim A/p`: both are transcendence degrees over `k`, and `κ(q)` is algebraic over
`κ(p)`. -/
theorem ringKrullDim_quotient_eq_of_forall (k : Type u) [Field k] [Algebra k A] [Algebra k B]
    [IsScalarTower k A B] [Algebra.FiniteType k A] [Algebra.FiniteType A B]
    (q : Ideal B) [q.IsPrime]
    (hq : ∀ q' : Ideal B, q'.IsPrime → q ≤ q' →
      q'.comap (algebraMap A B) = q.comap (algebraMap A B) → q' = q) :
    ringKrullDim (B ⧸ q) = ringKrullDim (A ⧸ q.comap (algebraMap A B)) := by
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans ‹_› ‹_›
  set p := q.comap (algebraMap A B)
  let := (Ideal.ResidueField.map p q (algebraMap A B) rfl).toAlgebra
  have : Algebra.IsAlgebraic p.ResidueField q.ResidueField := isAlgebraic_residueField q hq
  have : IsScalarTower k p.ResidueField q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = Ideal.ResidueField.map p q (algebraMap A B) rfl (algebraMap k _ c)
    rw [IsScalarTower.algebraMap_apply k A p.ResidueField, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply k A B, ← IsScalarTower.algebraMap_apply k B q.ResidueField]
  have : FaithfulSMul p.ResidueField q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (RingHom.injective (algebraMap p.ResidueField q.ResidueField))
  have : FaithfulSMul k p.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective (algebraMap k _))
  have htr := trdeg_add_eq k p.ResidueField (A := q.ResidueField)
  rw [trdeg_eq_zero (R := p.ResidueField) (A := q.ResidueField), add_zero] at htr
  obtain ⟨s, hs, hts⟩ := exists_ringKrullDim_eq_trdeg k (B ⧸ q) q.ResidueField
  obtain ⟨s', hs', hts'⟩ := exists_ringKrullDim_eq_trdeg k (A ⧸ p) p.ResidueField
  have : (s : Cardinal) = s' := hts.symm.trans (htr.symm.trans hts')
  rw [hs, hs', show s = s' by exact_mod_cast this]

end Algebra

section Chart

/-- On an affine scheme, the height of a point in the specialization order is the dimension of
the quotient by the corresponding prime. -/
theorem height_spec_eq (R : CommRingCat.{u}) (q : PrimeSpectrum R) :
    (height (α := ↥(Spec R)) q : WithBot ℕ∞) = ringKrullDim (R ⧸ q.asIdeal) := by
  rw [ringKrullDim_quotient_eq_coheight, ← height_orderIso (specOrderIsoPrimeSpectrum R) q]
  rfl

/-- On a scheme of finite type over a field, heights of points are computed on any open
subscheme containing them. -/
theorem height_apply_of_isOpenImmersion {K : Type u} [Field K] {S T : Scheme.{u}}
    (s : S ⟶ Spec (.of K)) (hs : FiniteType s) (φ : T ⟶ S) [IsOpenImmersion φ] (t : T) :
    height (φ t) = height t := by
  have hle : ∀ a b : T, φ a ≤ φ b ↔ a ≤ b := fun a b =>
    φ.isOpenEmbedding.isInducing.specializes_iff
  have hsm : StrictMono φ := fun a b hab => by
    rw [lt_iff_le_not_ge, hle, hle]; exact lt_iff_le_not_ge.mp hab
  have hlt : ∀ a b : T, φ a < φ b ↔ a < b := fun a b => by
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle, hle]
  refine le_antisymm ?_ (height_le_height_apply_of_strictMono _ hsm t)
  have := hs.1
  have : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨N, hN, hC⟩ := catenaryAt_of_finiteType s hs (φ t)
  obtain ⟨x₀, ⟨⟨t₀, rfl⟩, hx₀cl⟩, hx₀c⟩ := nonempty_inter_closedPoints
    (Z := Set.range φ ∩ closure {φ t}) ⟨φ t, ⟨t, rfl⟩, subset_closure rfl⟩
    (φ.isOpenEmbedding.isOpen_range.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hx₀le : φ t₀ ≤ φ t := specializes_iff_mem_closure.mpr hx₀cl
  have h0 := hC (φ t₀) hx₀le
  rw [Scheme.height_of_isClosed hx₀c, zero_add] at h0
  obtain ⟨l, hl0, hlen⟩ := exists_series_of_coheight_eq_coe _ h0
  have hrange : ∀ i, ((l i : Set.Iic (φ t)) : S) ∈ Set.range φ := fun i => by
    have h1 : (⟨φ t₀, hx₀le⟩ : Set.Iic (φ t)) ≤ l i := hl0 ▸ l.monotone (Fin.zero_le i)
    exact (show ((l i : Set.Iic (φ t)) : S) ⤳ φ t₀ from h1).mem_open
      φ.isOpenEmbedding.isOpen_range ⟨t₀, rfl⟩
  choose c hc using hrange
  let l' : LTSeries T := ⟨l.length, c, fun i => by
    have : l i.castSucc < l i.succ := l.step i
    show c i.castSucc < c i.succ
    rw [← hlt, hc, hc]
    exact this⟩
  rw [hN, ← hlen]
  refine length_le_height (p := l') ?_
  rw [← hle]
  change φ (c (Fin.last _)) ≤ φ t
  rw [hc]
  exact (l (Fin.last _)).2

/-- Let `f : X → Y` be locally of finite type between schemes of finite type over `k`, and let
`x ∈ X` be minimal in its fibre for the specialization order (that is, closed in its fibre).
Then `x` and `f x` have the same height, i.e. `dim cl{x} = dim cl{f x}`. -/
theorem height_eq_height_of_forall {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (hsX : FiniteType sX) (hsY : FiniteType sY)
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) (hmin : ∀ z, z ≤ x → f z = f x → z = x) :
    height x = height (f x) := by
  have := hsX.1
  have := hsY.1
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨x₀, hx₀cl, hx₀c⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show f x₀ ∈ (⊤ : Y.Opens) from trivial)
      isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x₀ ∈ f ⁻¹ᵁ V from hyV) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  have hV : IsAffineOpen V := hV
  have hxU' : x ∈ U := (specializes_iff_mem_closure.mpr hx₀cl).mem_open U.isOpen hxU
  let φ := f.appLE V U hUV
  have hcomm := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
  obtain ⟨q, rfl⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  have hfx' : ∀ r, f (hU.fromSpec r) = hV.fromSpec (Spec.map φ r) := fun r => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm]
  have hfx := hfx' q
  rw [hfx, height_apply_of_isOpenImmersion sX hsX, height_apply_of_isOpenImmersion sY hsY]
  apply WithBot.coe_injective
  refine (height_spec_eq _ q).trans (Eq.trans ?_ (height_spec_eq _ (Spec.map φ q)).symm)
  obtain ⟨_, _⟩ := DimensionCodimension.exists_algebra_finiteType sY hsY V hV
  let : Algebra Γ(Y, V) Γ(X, U) := φ.hom.toAlgebra
  let : Algebra k Γ(X, U) := ((algebraMap Γ(Y, V) Γ(X, U)).comp (algebraMap k Γ(Y, V))).toAlgebra
  have : IsScalarTower k Γ(Y, V) Γ(X, U) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType Γ(Y, V) Γ(X, U) := f.finiteType_appLE hV hU hUV
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  refine ringKrullDim_quotient_eq_of_forall k q.asIdeal fun q' hq' hle hcomap => ?_
  have hz : hU.fromSpec ⟨q', hq'⟩ ≤ hU.fromSpec q :=
    ((PrimeSpectrum.le_iff_specializes q ⟨q', hq'⟩).mp hle).map hU.fromSpec.continuous
  have hfz : f (hU.fromSpec ⟨q', hq'⟩) = f (hU.fromSpec q) := by
    rw [hfx]
    refine (hfx' (show ↥(Spec Γ(X, U)) from ⟨q', hq'⟩)).trans ?_
    congr 1
    exact PrimeSpectrum.ext hcomap
  have := hU.fromSpec.isOpenEmbedding.injective (hmin _ hz hfz)
  exact congrArg PrimeSpectrum.asIdeal this

end Chart

section Components

variable {S : Scheme.{u}}

/-- In a Noetherian Jacobson scheme, every irreducible component contains a closed point all of
whose generalizations lie in that component (a closed point on no other component). -/
theorem exists_isClosed_forall_mem [NoetherianSpace S] [JacobsonSpace S] {Z : Set S}
    (hZ : Z ∈ irreducibleComponents S) :
    ∃ x ∈ Z, IsClosed ({x} : Set S) ∧ ∀ z, x ≤ z → z ∈ Z := by
  obtain ⟨o, ho, hne, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨x, hxo, hxc⟩ := nonempty_inter_closedPoints hne ho.isLocallyClosed
  exact ⟨x, hoZ hxo, hxc, fun z hz => hoZ (hz.mem_open ho hxo)⟩

/-- An irreducible component is the closure of a point. -/
theorem exists_closure_eq {Z : Set S} (hZ : Z ∈ irreducibleComponents S) :
    ∃ ζ : S, closure {ζ} = Z :=
  (QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)).imp fun _ h => h

/-- If every irreducible component of `S` has dimension `D`, then every point of `S` lies below
a point of height `D`. -/
theorem exists_le_height_eq {D : ℕ}
    (h : ∀ Z ∈ irreducibleComponents S, topologicalKrullDim Z = D) (z : S) :
    ∃ g : S, z ≤ g ∧ height g = D := by
  obtain ⟨g, hg⟩ := exists_closure_eq (irreducibleComponent_mem_irreducibleComponents z)
  refine ⟨g, specializes_iff_mem_closure.mpr (hg ▸ mem_irreducibleComponent), ?_⟩
  have := h _ (irreducibleComponent_mem_irreducibleComponents z)
  rw [← hg, topologicalKrullDim_closure_singleton] at this
  exact_mod_cast this

end Components

end FlatEquidimensional

open FlatEquidimensional

/-- **Hartshorne III Corollary 9.6.** Let `f : X → Y` be a flat morphism of schemes of finite
type over a field `k`, with `Y` irreducible, and let `n` be a natural number. Every irreducible
component of `X` has dimension `dim Y + n` if and only if, for every point `y ∈ Y` (closed or
not), every irreducible component of the scheme-theoretic fibre `X_y` has dimension `n`. -/
theorem forall_irreducibleComponents_topologicalKrullDim_eq_add_iff {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (f : X ⟶ Y) (hf : Flat f.left)
    [IrreducibleSpace Y.left] (n : ℕ) :
    (∀ Z ∈ irreducibleComponents X.left,
        topologicalKrullDim Z = topologicalKrullDim Y.left + n) ↔
      ∀ y : Y.left, ∀ Z ∈ irreducibleComponents (f.left.fiber y), topologicalKrullDim Z = n := by
  have : LocallyOfFiniteType X.hom := hX.1
  have : LocallyOfFiniteType Y.hom := hY.1
  have : QuasiCompact X.hom := hX.2
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
    exact locallyOfFiniteType_of_comp f.left Y.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hFft : ∀ y : Y.left, FiniteType (f.left.fiberToSpecResidueField y) :=
    fun y => ⟨inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _)),
      inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))⟩
  have hFnoeth : ∀ y : Y.left, IsNoetherian (f.left.fiber y) := fun y => by
    have : LocallyOfFiniteType (f.left.fiberToSpecResidueField y) := (hFft y).1
    have : IsLocallyNoetherian (f.left.fiber y) :=
      LocallyOfFiniteType.isLocallyNoetherian (f.left.fiberToSpecResidueField y)
    exact {}
  have hCX : ∀ g : X.left, CatenaryAt g := catenaryAt_of_finiteType X.hom hX
  have hCY : ∀ g : Y.left, CatenaryAt g := catenaryAt_of_finiteType Y.hom hY
  have hCF : ∀ (y : Y.left) (g : f.left.fiber y), CatenaryAt g := fun y =>
    catenaryAt_of_finiteType (K := Y.left.residueField y) _ (hFft y)
  -- The base: `dim Y = height η` for the generic point `η`.
  have hη : ∀ z : Y.left, z ≤ genericPoint Y.left := fun z => genericPoint_specializes z
  obtain ⟨d, hd, -⟩ := hCY (genericPoint Y.left)
  have hdimY : topologicalKrullDim Y.left = ((d : ℕ∞) : WithBot ℕ∞) := by
    have h1 := topologicalKrullDim_closure_singleton (genericPoint Y.left)
    rw [(genericPoint_spec Y.left).def, hd] at h1
    rw [← h1, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y.left).isHomeomorph]
  have hYpt : ∀ y : Y.left, coheight y + height y = d := fun y => by
    rw [coheight_add_height_eq_of_forall (hCY _) (hη y) (fun z _ => hη z), hd]
  -- Proposition 9.5 at the points of the fibres.
  have hfib : ∀ (y : Y.left) (x : f.left.fiber y), f.left (f.left.fiberι y x) = y := fun y x => by
    have : f.left.fiberι y x ∈ Set.range (f.left.fiberι y) := ⟨x, rfl⟩
    rwa [Scheme.Hom.range_fiberι] at this
  have h95 : ∀ (y : Y.left) (x : f.left.fiber y),
      (coheight x : WithBot ℕ∞) + coheight y = coheight (f.left.fiberι y x) := by
    have key : ∀ (y₁ y₂ : Y.left), y₁ = y₂ → ∀ (x₁ : f.left.fiber y₁) (x₂ : f.left.fiber y₂),
        f.left.fiberι y₁ x₁ = f.left.fiberι y₂ x₂ →
          (coheight x₁ : WithBot ℕ∞) + coheight y₁ = coheight x₂ + coheight y₂ := by
      rintro y₁ _ rfl x₁ x₂ hx
      rw [(f.left.fiberι y₁).isEmbedding.injective hx]
    intro y x
    have h := ringKrullDim_stalk_fiber_add_ringKrullDim_stalk_of_flat hX hY f hf
      (f.left.fiberι y x)
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      ringKrullDim_stalk_eq_coheight] at h
    rw [← h]
    exact (key _ _ (hfib y x) _ _ (Scheme.Hom.fiberι_asFiber _ _)).symm
  constructor
  · -- (i) ⇒ (ii)
    intro h y Z hZ
    have := hFnoeth y
    obtain ⟨x, hxZ, hxc, hxup⟩ := exists_isClosed_forall_mem hZ
    obtain ⟨ζ, hζ⟩ := exists_closure_eq hZ
    have hmemZ : ∀ z, z ∈ Z ↔ z ≤ ζ := fun z => by
      rw [← hζ]; exact specializes_iff_mem_closure.symm
    have hx1 : coheight x = height ζ := by
      have := coheight_add_height_eq_of_forall (hCF y ζ) ((hmemZ x).mp hxZ)
        (fun z hz => (hmemZ z).mp (hxup z hz))
      rwa [Scheme.height_of_isClosed hxc, add_zero] at this
    have hDX : ∀ z : X.left, ∃ g, z ≤ g ∧ height g = ((d + n : ℕ) : ℕ∞) :=
      exists_le_height_eq (D := d + n) (fun Z hZ => by rw [h Z hZ, hdimY]; norm_cast)
    have hX1 := coheight_add_height_eq_of_equidim hCX hDX (f.left.fiberι y x)
    have hmin : ∀ z, z ≤ f.left.fiberι y x → f.left z = f.left (f.left.fiberι y x) →
        z = f.left.fiberι y x := by
      intro z hz hfz
      rw [hfib] at hfz
      obtain ⟨z', rfl⟩ : z ∈ Set.range (f.left.fiberι y) := by
        rw [Scheme.Hom.range_fiberι]; exact hfz
      have hz' : x ⤳ z' := (f.left.fiberι y).isEmbedding.isInducing.specializes_iff.mp hz
      rw [hz'.mem_closed hxc rfl]
    have hD := height_eq_height_of_forall X.hom Y.hom hX hY f.left _ hmin
    rw [hfib] at hD
    have h1 : coheight x + coheight y = coheight (f.left.fiberι y x) := by
      exact_mod_cast h95 y x
    have h2 := hYpt y
    rw [← hD] at h2
    obtain ⟨m, hm⟩ : ∃ m : ℕ, height (f.left.fiberι y x) = m :=
      ENat.ne_top_iff_exists.mp (fun ht => by rw [ht, add_top] at h2; exact ENat.top_ne_natCast _ h2)
        |>.imp fun _ e => e.symm
    obtain ⟨c₁, hc₁⟩ : ∃ c : ℕ, coheight y = c :=
      ENat.ne_top_iff_exists.mp (fun ht => by rw [ht, top_add] at h2; exact ENat.top_ne_natCast _ h2)
        |>.imp fun _ e => e.symm
    obtain ⟨c₂, hc₂⟩ : ∃ c : ℕ, coheight (f.left.fiberι y x) = c :=
      ENat.ne_top_iff_exists.mp
        (fun ht => by rw [ht, top_add] at hX1; exact ENat.top_ne_natCast _ hX1)
        |>.imp fun _ e => e.symm
    obtain ⟨c₃, hc₃⟩ : ∃ c : ℕ, coheight x = c :=
      ENat.ne_top_iff_exists.mp
        (fun ht => by rw [ht, top_add, hc₂] at h1; exact ENat.top_ne_natCast _ h1)
        |>.imp fun _ e => e.symm
    rw [hm, hc₁] at h2
    rw [hm, hc₂] at hX1
    rw [hc₁, hc₂, hc₃] at h1
    have e1 : c₁ + m = d := by exact_mod_cast h2
    have e2 : c₂ + m = d + n := by exact_mod_cast hX1
    have e3 : c₃ + c₁ = c₂ := by exact_mod_cast h1
    rw [← hζ, topologicalKrullDim_closure_singleton, ← hx1, hc₃]
    norm_cast
    omega
  · -- (ii) ⇒ (i)
    intro h Z hZ
    obtain ⟨x, hxZ, hxc, hxup⟩ := exists_isClosed_forall_mem hZ
    obtain ⟨ζ, hζ⟩ := exists_closure_eq hZ
    have hmemZ : ∀ z, z ∈ Z ↔ z ≤ ζ := fun z => by
      rw [← hζ]; exact specializes_iff_mem_closure.symm
    have hx1 : coheight x = height ζ := by
      have := coheight_add_height_eq_of_forall (hCX ζ) ((hmemZ x).mp hxZ)
        (fun z hz => (hmemZ z).mp (hxup z hz))
      rwa [Scheme.height_of_isClosed hxc, add_zero] at this
    have hyc : IsClosed {f.left x} := f.left.closePoints_subset_preimage_closedPoints hxc
    have hy1 : coheight (f.left x) = d := by
      have := hYpt (f.left x)
      rwa [Scheme.height_of_isClosed hyc, add_zero] at this
    have := hFnoeth (f.left x)
    have hx'c : IsClosed {f.left.asFiber x} := by
      have : ({f.left.asFiber x} : Set (f.left.fiber (f.left x))) =
          f.left.fiberι (f.left x) ⁻¹' {x} := by
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        rw [← (f.left.fiberι (f.left x)).isEmbedding.injective.eq_iff,
          Scheme.Hom.fiberι_asFiber]
      rw [this]
      exact hxc.preimage (f.left.fiberι _).continuous
    have hx'1 : coheight (f.left.asFiber x) = n := by
      have := coheight_add_height_eq_of_equidim (hCF (f.left x))
        (exists_le_height_eq (h (f.left x))) (f.left.asFiber x)
      rwa [Scheme.height_of_isClosed hx'c, add_zero] at this
    have h1 := h95 (f.left x) (f.left.asFiber x)
    rw [Scheme.Hom.fiberι_asFiber, hx'1, hy1, hx1] at h1
    rw [← hζ, topologicalKrullDim_closure_singleton, hdimY, ← h1]
    push_cast
    exact add_comm _ _

end Hartshorne
