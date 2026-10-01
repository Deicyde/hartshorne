/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.GradedAnnihilator
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Graded prime filtrations

Hartshorne, *Algebraic Geometry*, Proposition I.7.4 (pp. 50-51).
-/

namespace Hartshorne

open DirectSum

noncomputable section

variable {R A M : Type*}
  [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (𝓐 : ℤ → Submodule R A) [GradedAlgebra 𝓐]
  (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝓐 ℳ]

/-- The additive group structure on the carrier of a homogeneous submodule,
induced by its module structure over the ring `A`. -/
noncomputable instance homogeneousSubmoduleAddCommGroup
    (N : HomogeneousSubmodule 𝓐 ℳ) : AddCommGroup N :=
  Module.addCommMonoidToAddCommGroup A

noncomputable instance homogeneousSubmoduleOrderBot :
    OrderBot (HomogeneousSubmodule 𝓐 ℳ) where
  bot :=
    { toSubmodule := ⊥
      is_homogeneous' := by
        intro d m hm
        simp only [Submodule.mem_bot] at hm ⊢
        subst m
        simp }
  bot_le N := by
    change (⊥ : Submodule A M) ≤ N.toSubmodule
    exact bot_le

noncomputable instance homogeneousSubmoduleOrderTop :
    OrderTop (HomogeneousSubmodule 𝓐 ℳ) where
  top :=
    { toSubmodule := ⊤
      is_homogeneous' := fun _ _ _ ↦ trivial }
  le_top N := by
    change N.toSubmodule ≤ (⊤ : Submodule A M)
    exact le_top

/-- The sum of two homogeneous submodules is homogeneous. -/
noncomputable def homogeneousSubmoduleSup
    (N P : HomogeneousSubmodule 𝓐 ℳ) : HomogeneousSubmodule 𝓐 ℳ where
  toSubmodule := N.toSubmodule ⊔ P.toSubmodule
  is_homogeneous' := by
    intro d m hm
    rw [Submodule.mem_sup] at hm
    obtain ⟨n, hn, p, hp, rfl⟩ := hm
    rw [DirectSum.decompose_add]
    exact Submodule.add_mem_sup (N.isHomogeneous d hn) (P.isHomogeneous d hp)

private def submodulePieceToAmbient
    (N : HomogeneousSubmodule 𝓐 ℳ) (d : ℤ) :
    gradedSubmodulePiece 𝓐 ℳ N d →+ ℳ d where
  toFun x := ⟨x.1.1, x.2⟩
  map_zero' := by ext; rfl
  map_add' x y := by ext; rfl

private theorem coe_map_submodulePieceToAmbient
    (N : HomogeneousSubmodule 𝓐 ℳ)
    (z : ⨁ d, gradedSubmodulePiece 𝓐 ℳ N d) :
    DirectSum.coeAddMonoidHom ℳ
        (DirectSum.map (submodulePieceToAmbient 𝓐 ℳ N) z) =
      ((DirectSum.coeAddMonoidHom (gradedSubmodulePiece 𝓐 ℳ N) z : N) : M) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      exact congrArg (fun q : N => (q : M))
        (map_add (DirectSum.coeAddMonoidHom
          (gradedSubmodulePiece 𝓐 ℳ N)) x y).symm
  | of d x =>
      simp only [DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
      rfl

/-- Decomposing an element of a homogeneous submodule with its induced
grading gives the same homogeneous components as decomposing it in the
ambient module. -/
theorem coe_decompose_gradedSubmodulePiece
    (N : HomogeneousSubmodule 𝓐 ℳ) (n : N) (d : ℤ) :
    (((DirectSum.decompose (gradedSubmodulePiece 𝓐 ℳ N) n d :
        gradedSubmodulePiece 𝓐 ℳ N d) : N) : M) =
      (DirectSum.decompose ℳ (n : M) d : M) := by
  have hmap :
      DirectSum.map (submodulePieceToAmbient 𝓐 ℳ N)
          (DirectSum.decompose (gradedSubmodulePiece 𝓐 ℳ N) n) =
        DirectSum.decompose ℳ (n : M) := by
    apply (DirectSum.Decomposition.isInternal (ℳ := ℳ)).injective
    rw [coe_map_submodulePieceToAmbient]
    rw [show DirectSum.coeAddMonoidHom (gradedSubmodulePiece 𝓐 ℳ N)
        (DirectSum.decompose (gradedSubmodulePiece 𝓐 ℳ N) n) = n from
      (DirectSum.decompose (gradedSubmodulePiece 𝓐 ℳ N)).symm_apply_apply n]
    exact ((DirectSum.decompose ℳ).symm_apply_apply (n : M)).symm
  have hd := DFunLike.congr_fun hmap d
  rw [DirectSum.map_apply] at hd
  exact congrArg (fun q : ℳ d => (q : M)) hd

omit [IsScalarTower R A M] in
include 𝓐 in
/-- In a nonzero Noetherian graded module, some nonzero homogeneous element
has prime annihilator. -/
theorem exists_homogeneous_torsionOf_isPrime
    [IsNoetherianRing A] [Nontrivial M] :
    ∃ (l : ℤ) (m : M), m ∈ ℳ l ∧ m ≠ 0 ∧
      (Ideal.torsionOf A M m).IsPrime := by
  classical
  have hex : ∃ z : Σ l : ℤ, ℳ l, (z.2 : M) ≠ 0 := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    have hdec : DirectSum.decompose ℳ m ≠ 0 := by
      intro hzero
      apply hm
      apply (DirectSum.decompose ℳ).injective
      simpa using hzero
    have hsupp : (DirectSum.decompose ℳ m).support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      exact fun h ↦ hdec (DFinsupp.support_eq_empty.mp h)
    obtain ⟨l, hl⟩ := hsupp
    refine ⟨⟨l, DirectSum.decompose ℳ m l⟩, ?_⟩
    intro hzero
    exact (DFinsupp.mem_support_iff.mp hl) (Subtype.ext hzero)
  obtain ⟨z, hz⟩ := exists_maximalFor_of_wellFoundedGT
    (fun z : Σ l : ℤ, ℳ l ↦ (z.2 : M) ≠ 0)
    (fun z ↦ Ideal.torsionOf A M (z.2 : M)) hex
  refine ⟨z.1, z.2, z.2.property, hz.1, ?_⟩
  have hhom := torsionOf_isHomogeneous 𝓐 ℳ z.2.property
  apply hhom.isPrime_of_homogeneous_mem_or_mem
    (torsionOf_ne_top_of_ne_zero hz.1)
  intro a b _ha hb hab
  by_cases hbI : b ∈ Ideal.torsionOf A M (z.2 : M)
  · exact Or.inr hbI
  · left
    obtain ⟨j, hbj⟩ := hb
    let w : Σ l : ℤ, ℳ l :=
      ⟨j + z.1, ⟨b • (z.2 : M),
        SetLike.GradedSMul.smul_mem hbj z.2.property⟩⟩
    have hw : (w.2 : M) ≠ 0 := by
      intro hwzero
      apply hbI
      rw [Ideal.mem_torsionOf_iff]
      exact hwzero
    have hle : Ideal.torsionOf A M (z.2 : M) ≤
        Ideal.torsionOf A M (w.2 : M) := by
      intro r hr
      rw [Ideal.mem_torsionOf_iff] at hr ⊢
      change r • (b • (z.2 : M)) = 0
      rw [smul_smul, mul_comm, ← smul_smul, hr, smul_zero]
    have hmax : Ideal.torsionOf A M (w.2 : M) ≤
        Ideal.torsionOf A M (z.2 : M) := hz.2 hw hle
    apply hmax
    rw [Ideal.mem_torsionOf_iff] at hab ⊢
    change a • (b • (z.2 : M)) = 0
    rwa [smul_smul]

/-- A homogeneous submodule `N₁ ≤ N₂` regarded as a homogeneous submodule
of `N₂` with its induced grading. -/
noncomputable def gradedSubmoduleOf
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) (_h : N₁ ≤ N₂) :
    HomogeneousSubmodule 𝓐 (gradedSubmodulePiece 𝓐 ℳ N₂) where
  toSubmodule := N₁.toSubmodule.submoduleOf N₂.toSubmodule
  is_homogeneous' := by
    intro d n hn
    change (((DirectSum.decompose (gradedSubmodulePiece 𝓐 ℳ N₂) n d :
      gradedSubmodulePiece 𝓐 ℳ N₂ d) : N₂) : M) ∈ N₁
    rw [coe_decompose_gradedSubmodulePiece 𝓐 ℳ]
    exact N₁.isHomogeneous d hn

/-- The natural degree-`d` piece of the factor `N₂ / N₁`, for homogeneous
submodules `N₁ ≤ N₂`. -/
def gradedFactorPiece
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) (h : N₁ ≤ N₂) (d : ℤ) :
    Submodule R (N₂ ⧸ (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule) :=
  gradedQuotientPiece 𝓐 (gradedSubmodulePiece 𝓐 ℳ N₂)
    (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h) d

private def factorMap
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) :
    N₂.toSubmodule →ₗ[A] (M ⧸ N₁.toSubmodule) :=
  N₁.toSubmodule.mkQ.comp N₂.toSubmodule.subtype

private theorem factorMap_ker
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) (h : N₁ ≤ N₂) :
    LinearMap.ker (factorMap 𝓐 ℳ N₁ N₂) =
      (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule := by
  ext y
  change N₁.toSubmodule.mkQ (y : M) = 0 ↔ (y : M) ∈ N₁.toSubmodule
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

private theorem factorMap_range
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ)
    {x : M} {l : ℤ} (hx : x ∈ ℳ l)
    (hN₂ : N₂ = homogeneousSubmoduleSup 𝓐 ℳ N₁
      (gradedCyclicSubmodule 𝓐 ℳ hx)) :
    LinearMap.range (factorMap 𝓐 ℳ N₁ N₂) =
      (gradedCyclicSubmodule 𝓐
        (gradedQuotientPiece 𝓐 ℳ N₁)
        (show N₁.toSubmodule.mkQ x ∈
          gradedQuotientPiece 𝓐 ℳ N₁ l from ⟨x, hx, rfl⟩)).toSubmodule := by
  have hN₂' : N₂.toSubmodule =
      N₁.toSubmodule ⊔ (gradedCyclicSubmodule 𝓐 ℳ hx).toSubmodule := by
    exact congrArg HomogeneousSubmodule.toSubmodule hN₂
  rw [factorMap, LinearMap.range_comp, Submodule.range_subtype, hN₂', Submodule.map_sup]
  simp [gradedCyclicSubmodule, Submodule.map_span]

/-- The natural linear equivalence from a filtration factor obtained by
adjoining one homogeneous element to the cyclic submodule generated by its
class in the preceding quotient. -/
noncomputable def factorToCyclicEquiv
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) (h : N₁ ≤ N₂)
    {x : M} {l : ℤ} (hx : x ∈ ℳ l)
    (hN₂ : N₂ = homogeneousSubmoduleSup 𝓐 ℳ N₁
      (gradedCyclicSubmodule 𝓐 ℳ hx)) :
    (N₂ ⧸ (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule) ≃ₗ[A]
      gradedCyclicSubmodule 𝓐 (gradedQuotientPiece 𝓐 ℳ N₁)
        (show N₁.toSubmodule.mkQ x ∈ gradedQuotientPiece 𝓐 ℳ N₁ l from
          ⟨x, hx, rfl⟩) :=
  (Submodule.quotEquivOfEq _ _ (factorMap_ker 𝓐 ℳ N₁ N₂ h).symm).trans
    ((LinearMap.quotKerEquivRange (factorMap 𝓐 ℳ N₁ N₂)).trans
      (LinearEquiv.ofEq _ _ (factorMap_range 𝓐 ℳ N₁ N₂ hx hN₂)))

@[simp]
theorem coe_factorToCyclicEquiv_mk
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) (h : N₁ ≤ N₂)
    {x : M} {l : ℤ} (hx : x ∈ ℳ l)
    (hN₂ : N₂ = homogeneousSubmoduleSup 𝓐 ℳ N₁
      (gradedCyclicSubmodule 𝓐 ℳ hx)) (y : N₂.toSubmodule) :
    ((factorToCyclicEquiv 𝓐 ℳ N₁ N₂ h hx hN₂
      (Submodule.Quotient.mk y) :
        gradedCyclicSubmodule 𝓐 (gradedQuotientPiece 𝓐 ℳ N₁)
          (show N₁.toSubmodule.mkQ x ∈ gradedQuotientPiece 𝓐 ℳ N₁ l from
            ⟨x, hx, rfl⟩)) : M ⧸ N₁.toSubmodule) =
      N₁.toSubmodule.mkQ (y : M) := by
  rfl

/-- The natural equivalence between a one-generator factor and the cyclic
submodule generated by the class of that generator is graded. -/
noncomputable def gradedFactorToCyclicEquiv
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) (h : N₁ ≤ N₂)
    {x : M} {l : ℤ} (hx : x ∈ ℳ l)
    (hN₂ : N₂ = homogeneousSubmoduleSup 𝓐 ℳ N₁
      (gradedCyclicSubmodule 𝓐 ℳ hx)) :
    GradedLinearEquiv A
      (gradedFactorPiece 𝓐 ℳ N₁ N₂ h)
      (gradedSubmodulePiece 𝓐 (gradedQuotientPiece 𝓐 ℳ N₁)
        (gradedCyclicSubmodule 𝓐 (gradedQuotientPiece 𝓐 ℳ N₁)
          (show N₁.toSubmodule.mkQ x ∈ gradedQuotientPiece 𝓐 ℳ N₁ l from
            ⟨x, hx, rfl⟩))) where
  toLinearEquiv := factorToCyclicEquiv 𝓐 ℳ N₁ N₂ h hx hN₂
  map_piece d := by
    ext c
    constructor
    · rintro ⟨q, hq, rfl⟩
      change q ∈ gradedQuotientPiece 𝓐
        (gradedSubmodulePiece 𝓐 ℳ N₂)
        (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h) d at hq
      obtain ⟨y, hy, rfl⟩ := hq
      change N₁.toSubmodule.mkQ ((y : N₂) : M) ∈
        gradedQuotientPiece 𝓐 ℳ N₁ d
      exact ⟨((y : N₂) : M), hy, rfl⟩
    · intro hc
      change (c : M ⧸ N₁.toSubmodule) ∈
        gradedQuotientPiece 𝓐 ℳ N₁ d at hc
      obtain ⟨z, hz, hzc⟩ := hc
      have hcRange : (c : M ⧸ N₁.toSubmodule) ∈
          LinearMap.range (factorMap 𝓐 ℳ N₁ N₂) := by
        rw [factorMap_range 𝓐 ℳ N₁ N₂ hx hN₂]
        exact c.property
      obtain ⟨y, hyc⟩ := hcRange
      have hdiff : z - (y : M) ∈ N₁.toSubmodule := by
        rw [← Submodule.Quotient.eq]
        calc
          Submodule.Quotient.mk z = (c : M ⧸ N₁.toSubmodule) := hzc
          _ = factorMap 𝓐 ℳ N₁ N₂ y := hyc.symm
          _ = Submodule.Quotient.mk (y : M) := rfl
      have hzN₂ : z ∈ N₂ := by
        have hsum : z - (y : M) + (y : M) ∈ N₂.toSubmodule :=
          N₂.toSubmodule.add_mem (h hdiff) y.property
        rwa [sub_add_cancel] at hsum
      let y' : N₂.toSubmodule := ⟨z, hzN₂⟩
      let yd : gradedSubmodulePiece 𝓐 ℳ N₂ d := ⟨y', hz⟩
      refine ⟨Submodule.Quotient.mk y', ?_, ?_⟩
      · change Submodule.Quotient.mk y' ∈ gradedQuotientPiece 𝓐
          (gradedSubmodulePiece 𝓐 ℳ N₂)
          (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h) d
        exact ⟨yd, yd.property, rfl⟩
      · apply Subtype.ext
        rw [coe_factorToCyclicEquiv_mk]
        exact hzc

/-- A homogeneous ideal, viewed as a homogeneous submodule of the graded
ring. -/
def homogeneousIdealSubmodule (p : Ideal A) (hp : p.IsHomogeneous 𝓐) :
    HomogeneousSubmodule 𝓐 𝓐 where
  toSubmodule := p
  is_homogeneous' := hp

/-- One step in a graded prime filtration.  The step records the inclusion,
the homogeneous prime, the twist, and a graded equivalence with the natural
grading on the subquotient. -/
def IsGradedPrimeFiltrationStep
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) : Prop :=
  ∃ h : N₁ ≤ N₂, ∃ p : PrimeSpectrum A,
    ∃ hp : p.1.IsHomogeneous 𝓐, ∃ l : ℤ,
      Nonempty <| GradedLinearEquiv A
        (gradedModuleTwist
          (gradedQuotientPiece 𝓐 𝓐 (homogeneousIdealSubmodule 𝓐 p.1 hp)) l)
        (gradedFactorPiece 𝓐 ℳ N₁ N₂ h)

/-- Every proper homogeneous submodule admits a strictly larger homogeneous
extension whose factor is a twist of a quotient by a homogeneous prime. -/
theorem exists_gradedPrimeFiltrationStep
    [IsNoetherianRing A] [Module.Finite A M]
    (N : HomogeneousSubmodule 𝓐 ℳ) (hN : N ≠ ⊤) :
    ∃ N' > N, IsGradedPrimeFiltrationStep 𝓐 ℳ N N' := by
  have hNtop : N.toSubmodule ≠ ⊤ := by
    intro htop
    apply hN
    apply HomogeneousSubmodule.ext
    exact htop
  let _ : Nontrivial (M ⧸ N.toSubmodule) :=
    Submodule.Quotient.nontrivial_iff.mpr hNtop
  obtain ⟨l, q, hq, hq0, hp⟩ :=
    exists_homogeneous_torsionOf_isPrime 𝓐
      (gradedQuotientPiece 𝓐 ℳ N)
  obtain ⟨x, hx, hxq⟩ := hq
  have hxN : x ∉ N := by
    intro hxmem
    apply hq0
    rw [← hxq]
    exact (Submodule.Quotient.mk_eq_zero N.toSubmodule).2 hxmem
  let N' : HomogeneousSubmodule 𝓐 ℳ :=
    homogeneousSubmoduleSup 𝓐 ℳ N (gradedCyclicSubmodule 𝓐 ℳ hx)
  have hle : N ≤ N' := by
    intro m hm
    exact Submodule.mem_sup_left hm
  have hxN' : x ∈ N' := by
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hlt : N < N' :=
    lt_iff_le_and_ne.mpr ⟨hle, fun heq ↦ hxN (heq.symm ▸ hxN')⟩
  have hq' : N.toSubmodule.mkQ x ∈ gradedQuotientPiece 𝓐 ℳ N l :=
    ⟨x, hx, rfl⟩
  have hqeq : q = N.toSubmodule.mkQ x := hxq.symm
  subst q
  refine ⟨N', hlt, hle,
    ⟨Ideal.torsionOf A (M ⧸ N.toSubmodule) (N.toSubmodule.mkQ x), hp⟩,
    torsionOf_isHomogeneous 𝓐 (gradedQuotientPiece 𝓐 ℳ N) hq',
    -l, ?_⟩
  refine ⟨(gradedCyclicModuleEquiv 𝓐
    (gradedQuotientPiece 𝓐 ℳ N) hq').trans ?_⟩
  exact (gradedFactorToCyclicEquiv 𝓐 ℳ N N' hle hx rfl).symm

noncomputable instance homogeneousSubmoduleWellFoundedGT
    [IsNoetherianRing A] [Module.Finite A M] :
    WellFoundedGT (HomogeneousSubmodule 𝓐 ℳ) := by
  let e :
      ((· > ·) : HomogeneousSubmodule 𝓐 ℳ →
        HomogeneousSubmodule 𝓐 ℳ → Prop) ↪r
      ((· > ·) : Submodule A M → Submodule A M → Prop) :=
    { toFun := HomogeneousSubmodule.toSubmodule
      inj' := HomogeneousSubmodule.toSubmodule_injective 𝓐 ℳ
      map_rel_iff' := Iff.rfl }
  exact e.isWellFounded

/-- A finite increasing series of homogeneous submodules from `0` to `M`
whose every factor is graded-linearly equivalent to a twist of `A / p` for a
homogeneous prime ideal `p`. -/
theorem exists_gradedPrimeFiltration
    [IsNoetherianRing A] [Module.Finite A M] :
    ∃ s : RelSeries
        {p : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
          IsGradedPrimeFiltrationStep 𝓐 ℳ p.1 p.2},
      s.head = ⊥ ∧ s.last = ⊤ := by
  refine WellFoundedGT.induction_top
    ⟨⊥, RelSeries.singleton _ ⊥, rfl, rfl⟩ ?_
  rintro N hN ⟨s, hshead, hslast⟩
  obtain ⟨N', hNN', hstep⟩ :=
    exists_gradedPrimeFiltrationStep 𝓐 ℳ N hN
  refine ⟨N', hNN', s.snoc N' (hslast ▸ hstep), ?_, ?_⟩
  · simpa using hshead
  · simp

end


end Hartshorne
