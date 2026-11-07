/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveIntersectionDivisor
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Codimension-one points of an integral closed subscheme of projective space

Let `ℙⁿ_k = Proj k[x₀, ..., xₙ]` and let `ι : X ⟶ ℙⁿ_k` be a closed immersion of an integral
scheme. Write `𝔭` for the homogeneous prime of the image of the generic point of `X`, and for a
point `x` of `X` write `𝔓ₓ` for the homogeneous prime of `ι x`.

* `ι` identifies `X` with the closed set of homogeneous relevant primes containing `𝔭`, and
  `x ⤳ y` exactly when `𝔓ₓ ⊆ 𝔓_y`.
* Let `f` be homogeneous with `f ∉ 𝔭`. Then `x` is a codimension-one point of `X` lying on the
  hypersurface `f = 0` exactly when `𝔓ₓ` is a minimal prime of `𝔭 + (f)`; and every relevant minimal
  prime of `𝔭 + (f)` is some `𝔓ₓ`. The proof uses Krull's principal ideal theorem in `S / 𝔭`
  and the fact that a minimal prime over a homogeneous ideal is homogeneous.

These are the scheme-side half of the comparison between the divisor `V · X` of Hartshorne,
Exercise II.6.2, and the intersection multiplicities of Theorem I.7.7.

## Main results

* `Hartshorne.closedImmersion_specializes_iff`
* `Hartshorne.mem_range_closedImmersion_iff`
* `Hartshorne.coheight_eq_one_and_mem_iff_mem_minimalPrimes`
* `Hartshorne.exists_closedImmersion_eq_of_mem_minimalPrimes`
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- In a Noetherian ring, there is no prime strictly between a prime `p` and a prime `Q` minimal
over `p + (f)` (Krull's principal ideal theorem in `R / p`). -/
theorem not_lt_lt_of_mem_minimalPrimes_sup_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    {p q Q : Ideal R} [p.IsPrime] [q.IsPrime] {f : R}
    (hQ : Q ∈ (p ⊔ Ideal.span {f}).minimalPrimes) (hpq : p < q) (hqQ : q < Q) : False := by
  have hQp : Q.IsPrime := hQ.1.1
  let g := Ideal.Quotient.mk p
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = p := Ideal.mk_ker
  have hpQ : p ≤ Q := hpq.le.trans hqQ.le
  have hQm : (Q.map g).IsPrime := Ideal.map_isPrime_of_surjective hg (by rw [hker]; exact hpQ)
  have hqm : (q.map g).IsPrime := Ideal.map_isPrime_of_surjective hg (by rw [hker]; exact hpq.le)
  have hbot : (⊥ : Ideal (R ⧸ p)).IsPrime := Ideal.isPrime_bot
  have hcomap : ∀ I : Ideal R, p ≤ I → (I.map g).comap g = I := fun I hI ↦ by
    rw [Ideal.comap_map_of_surjective _ hg, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hI]
  have hmapstrict : ∀ I J : Ideal R, p ≤ I → p ≤ J → I < J → I.map g < J.map g :=
    fun I J hI hJ hIJ ↦ (Ideal.map_mono hIJ.le).lt_of_ne fun h ↦ hIJ.ne <| by
      rw [← hcomap I hI, ← hcomap J hJ, h]
  have h1 : (⊥ : Ideal (R ⧸ p)) < q.map g := by
    have : p.map g = ⊥ := by rw [Ideal.map_eq_bot_iff_le_ker, hker]
    rw [← this]
    exact hmapstrict p q le_rfl hpq.le hpq
  have h2 : q.map g < Q.map g := hmapstrict q Q hpq.le hpQ hqQ
  have hle : (Q.map g).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ
  have : (Q.map g).FiniteHeight :=
    ⟨Or.inr (hle.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have hlt2 := Ideal.height_strict_mono_of_isPrime_of_isPrime h2
  have : (q.map g).FiniteHeight :=
    ⟨Or.inr ((hlt2.trans_le hle).trans (WithTop.coe_lt_top 1)).ne⟩
  have hlt1 := Ideal.height_strict_mono_of_isPrime_of_isPrime h1
  have : (q.map g).height < 1 := hlt2.trans_le hle
  rw [Order.lt_one_iff] at this
  rw [this] at hlt1
  exact (not_lt_zero hlt1).elim

/-- A prime minimal over a homogeneous ideal is homogeneous. -/
theorem isHomogeneous_of_mem_minimalPrimes {A σ : Type*}
    [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {I Q : Ideal A} (hI : I.IsHomogeneous 𝒜) (hQ : Q ∈ I.minimalPrimes) :
    Q.IsHomogeneous 𝒜 := by
  have hQp : Q.IsPrime := hQ.1.1
  have hcore : ((Q.homogeneousCore 𝒜).toIdeal).IsPrime := hQp.homogeneousCore
  have hIcore : I ≤ (Q.homogeneousCore 𝒜).toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hQ.1.2
  have heq : (Q.homogeneousCore 𝒜).toIdeal = Q :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le 𝒜 Q)
      (hQ.2 ⟨hcore, hIcore⟩ (Ideal.toIdeal_homogeneousCore_le 𝒜 Q))
  rw [← heq]
  exact (Q.homogeneousCore 𝒜).isHomogeneous

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) k

local notation "S" => MvPolynomial (Fin (n + 1)) k

/-- Specialization in `ℙⁿ_k` is inclusion of homogeneous primes. -/
theorem proj_specializes_iff_le (x y : Proj 𝒜) :
    x ⤳ y ↔ x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal := by
  rw [specializes_iff_mem_closure]
  exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 x y).symm

variable {X : Scheme.{u}}

/-- Along a closed immersion into `ℙⁿ_k`, `x ⤳ y` exactly when the homogeneous prime of `ι x`
is contained in that of `ι y`. -/
theorem closedImmersion_specializes_iff (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (x y : X) :
    x ⤳ y ↔ (ι.base x).asHomogeneousIdeal ≤ (ι.base y).asHomogeneousIdeal := by
  rw [← proj_specializes_iff_le]
  exact (ι.isClosedEmbedding.isInducing.specializes_iff).symm

/-- The image of a closed immersion of an integral scheme into `ℙⁿ_k` consists of the points
whose homogeneous prime contains the prime `𝔭` of the image of the generic point. -/
theorem mem_range_closedImmersion_iff (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] [IsIntegral X]
    (q : Proj 𝒜) :
    q ∈ Set.range ι ↔ (ι.base (genericPoint X)).asHomogeneousIdeal ≤ q.asHomogeneousIdeal := by
  rw [← proj_specializes_iff_le]
  constructor
  · rintro ⟨x, rfl⟩
    exact (genericPoint_specializes x).map ι.continuous
  · intro h
    exact h.mem_closed ι.isClosedEmbedding.isClosed_range ⟨_, rfl⟩

/-- **Codimension-one points on a hypersurface.** Let `ι : X ⟶ ℙⁿ_k` be a closed immersion of an
integral scheme, `𝔭` the homogeneous prime of the image of the generic point, and `f` a
homogeneous polynomial not in `𝔭`. A point `x` of `X` has codimension one and lies on `f = 0`
exactly when the homogeneous prime of `ι x` is a minimal prime of `𝔭 + (f)`. -/
theorem coheight_eq_one_and_mem_iff_mem_minimalPrimes (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι]
    [IsIntegral X] {f : S} {d : ℕ}
    (hf : f.IsHomogeneous d) (hfX : f ∉ (ι.base (genericPoint X)).asHomogeneousIdeal) (x : X) :
    (Order.coheight x = 1 ∧ f ∈ (ι.base x).asHomogeneousIdeal) ↔
      (ι.base x).asHomogeneousIdeal.toIdeal ∈
        ((ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal ⊔ Ideal.span {f}).minimalPrimes := by
  set 𝔭 := (ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal with h𝔭
  have hle : ∀ y : X, 𝔭 ≤ (ι.base y).asHomogeneousIdeal.toIdeal := fun y ↦
    (closedImmersion_specializes_iff ι _ _).mp (genericPoint_specializes y)
  have hhom : (𝔭 ⊔ Ideal.span {f}).IsHomogeneous 𝒜 :=
    (ι.base (genericPoint X)).asHomogeneousIdeal.isHomogeneous.sup
      (Ideal.homogeneous_span _ _ fun g hg ↦ by
        rw [Set.mem_singleton_iff.mp hg]
        exact ⟨d, (mem_homogeneousSubmodule d f).mpr hf⟩)
  have hmaxgen : ∀ y : X, IsMax y → y = genericPoint X := fun y hmax ↦
    ((genericPoint_specializes y).antisymm (hmax (genericPoint_specializes y))).eq.symm
  have hne_gen : ∀ y : X, f ∈ (ι.base y).asHomogeneousIdeal → y ≠ genericPoint X := by
    rintro y hy rfl
    exact hfX hy
  constructor
  · rintro ⟨hx1, hfx⟩
    refine ⟨⟨(ι.base x).isPrime, sup_le (hle x) ((Ideal.span_singleton_le_iff_mem _).mpr hfx)⟩, ?_⟩
    intro Q ⟨hQp, hQ⟩ hQx
    -- the homogeneous core of `Q` is the prime of a point `y` with `x ≤ y`
    let Q' := Q.homogeneousCore 𝒜
    have hQ'p : Q'.toIdeal.IsPrime := hQp.homogeneousCore
    have hQ'le : Q'.toIdeal ≤ Q := Ideal.toIdeal_homogeneousCore_le 𝒜 Q
    have hsupQ' : 𝔭 ⊔ Ideal.span {f} ≤ Q'.toIdeal := by
      rw [← hhom.toIdeal_homogeneousCore_eq_self]
      exact Ideal.homogeneousCore_mono 𝒜 hQ
    have hrel : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ Q' := fun h ↦
      (ι.base x).not_irrelevant_le (h.trans fun a ha ↦ hQx (hQ'le ha))
    let q : Proj 𝒜 := ⟨Q', hQ'p, hrel⟩
    obtain ⟨y, hy⟩ := (mem_range_closedImmersion_iff ι q).mpr
      (fun a ha ↦ hsupQ' (le_sup_left (a := 𝔭) ha))
    have hyQ' : (ι.base y).asHomogeneousIdeal.toIdeal = Q'.toIdeal := by rw [hy]
    have hxy : x ≤ y := by
      change y ⤳ x
      rw [closedImmersion_specializes_iff ι]
      intro a ha
      exact hQx (hQ'le (hyQ' ▸ ha))
    have hfy : f ∈ (ι.base y).asHomogeneousIdeal := by
      change f ∈ (ι.base y).asHomogeneousIdeal.toIdeal
      rw [hyQ']
      exact hsupQ' (le_sup_right (b := Ideal.span {f}) (Ideal.mem_span_singleton_self f))
    have hy1 : 1 ≤ Order.coheight y := by
      rw [Order.one_le_iff_pos, Order.coheight_pos]
      intro hmax
      exact hne_gen y hfy (hmaxgen y hmax)
    by_cases hyx : y ≤ x
    · have h := (closedImmersion_specializes_iff ι x y).mp hyx
      exact fun a ha ↦ hQ'le (hyQ' ▸ h ha)
    · have := Order.coheight_add_one_le (lt_of_le_not_ge hxy hyx)
      rw [hx1] at this
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := (by gcongr : (1 : ℕ∞) + 1 ≤ Order.coheight y + 1).trans this
      exact absurd h2 (by decide)
  · intro hmin
    have hfx : f ∈ (ι.base x).asHomogeneousIdeal :=
      hmin.1.2 (le_sup_right (b := Ideal.span {f}) (Ideal.mem_span_singleton_self f))
    refine ⟨?_, hfx⟩
    have hxne := hne_gen x hfx
    apply le_antisymm
    · rw [Order.coheight_eq_iSup_gt_coheight]
      refine iSup₂_le fun y hxy ↦ ?_
      by_cases hyg : y = genericPoint X
      · rw [hyg, Order.coheight_eq_zero.mpr fun b _ ↦ genericPoint_specializes b, zero_add]
      · exfalso
        have hyg' : y < genericPoint X :=
          ⟨genericPoint_specializes y, fun h ↦ hyg ((genericPoint_specializes y).antisymm h).eq.symm⟩
        have hlt : ∀ {a b : X}, a < b →
            (ι.base b).asHomogeneousIdeal.toIdeal < (ι.base a).asHomogeneousIdeal.toIdeal := by
          intro a b hab
          refine lt_of_le_of_ne ((closedImmersion_specializes_iff ι b a).mp hab.1) fun h ↦
            hab.2 ?_
          rw [closedImmersion_specializes_iff ι]
          exact h.ge
        have : (ι.base y).asHomogeneousIdeal.toIdeal.IsPrime := (ι.base y).isPrime
        have : 𝔭.IsPrime := (ι.base (genericPoint X)).isPrime
        exact not_lt_lt_of_mem_minimalPrimes_sup_span hmin (hlt hyg') (hlt hxy)
    · rw [Order.one_le_iff_pos, Order.coheight_pos]
      intro hmax
      exact hxne (hmaxgen x hmax)

/-- Every relevant minimal prime of `𝔭 + (f)` is the homogeneous prime of a point of `X`. -/
theorem exists_closedImmersion_eq_of_mem_minimalPrimes (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι]
    [IsIntegral X] {f : S} {d : ℕ}
    (hf : f.IsHomogeneous d) {Q : Ideal S}
    (hQ : Q ∈ ((ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal ⊔ Ideal.span {f}).minimalPrimes)
    (hrel : ¬(HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Q) :
    ∃ x : X, (ι.base x).asHomogeneousIdeal.toIdeal = Q := by
  have hhom : ((ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal ⊔ Ideal.span {f}).IsHomogeneous 𝒜 :=
    (ι.base (genericPoint X)).asHomogeneousIdeal.isHomogeneous.sup
      (Ideal.homogeneous_span _ _ fun g hg ↦ by
        rw [Set.mem_singleton_iff.mp hg]
        exact ⟨d, (mem_homogeneousSubmodule d f).mpr hf⟩)
  have hQh := isHomogeneous_of_mem_minimalPrimes 𝒜 hhom hQ
  let q : Proj 𝒜 := ⟨⟨Q, hQh⟩, hQ.1.1, hrel⟩
  obtain ⟨x, hx⟩ := (mem_range_closedImmersion_iff ι q).mpr
    (fun a ha ↦ hQ.1.2 (le_sup_left (b := Ideal.span {f}) ha))
  exact ⟨x, by rw [hx]⟩

end Hartshorne
