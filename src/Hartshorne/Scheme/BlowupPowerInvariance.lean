/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ReesAlgebraBlowup
import Hartshorne.Scheme.VeroneseDuple
import Hartshorne.Scheme.InfinitesimalNeighborhoods
import Hartshorne.Scheme.IdealPowerProduct

/-!
# Blowing up a power of the center

Hartshorne, *Algebraic Geometry*, II, Exercise 7.11(a) (p. 171): for a coherent sheaf of ideals
`I` on a Noetherian scheme `X` and `d > 0`, the blowup of `X` along `Iᵈ` is canonically
isomorphic over `X` to the blowup along `I`.

## Proof

The sheaf of Rees algebras of `Iᵈ` is the `d`-th Veronese subalgebra of the sheaf of Rees
algebras of `I`: over an affine open `U`, with `J = Γ(U, I)`, the map `p(t) ↦ p(tᵈ)` identifies
`⨁ₙ (Jᵈ)ⁿ tⁿ` with `(⨁ₙ Jⁿ tⁿ)^{(d)} = ⨁ₙ Jⁿᵈ tⁿᵈ` as graded rings (`reesVeronese`). Composing
with the isomorphism `Proj S ≅ Proj S^{(d)}` of Exercise II.5.13 gives isomorphisms
`Proj Γ(U, ⨁ₙ Iⁿ) ≅ Proj Γ(U, ⨁ₙ Iⁿᵈ)` over `U` (`projReesPowIso`). They are compatible with
restriction to basic opens (`projReesPowIso_hom_naturality`, from the naturality of the Veronese
isomorphism, `Veronese.map_comp_toProj`), so they glue to an isomorphism of the relative `Proj`s
over `X`.

## Main definitions and results

* `reesVeronese`, `reesVeroneseInv`, `projReesVeroneseIso`: for `K = Jᵈ`, the graded ring
  isomorphism `⨁ₙ Kⁿ tⁿ ≅ (⨁ₙ Jⁿ tⁿ)^{(d)}` and the induced isomorphism of `Proj`s.
* `QuasicoherentIdealSubsheaf.isCoherent_pow`: on a Noetherian scheme, `Iᵏ` is coherent.
* `QuasicoherentIdealSubsheaf.blowupPowIso`, `blowupPowIso_hom_blowupProjection`: the isomorphism
  `Bl_{Iᵈ} X ≅ Bl_I X` over `X`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomogeneousIdeal
open AlgebraicGeometry

universe u

namespace Hartshorne

/-! ### Irrelevant ideals under graded maps -/

section Irrelevant

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- If a graded ring map `f` has a graded right inverse `g`, then `ℬ₊ ⊆ f(𝒜₊) ℬ`. -/
theorem irrelevant_le_map_of_rightInverse (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (h : ∀ x, f (g x) = x) : ℬ₊ ≤ 𝒜₊.map f := by
  intro x hx
  change x ∈ Ideal.map f (𝒜₊).toIdeal
  rw [← h x]
  refine Ideal.mem_map_of_mem _ ?_
  change GradedRing.proj 𝒜 0 (g x) = 0
  have hx' : GradedRing.proj ℬ 0 x = 0 := hx
  simp only [GradedRing.proj_apply] at hx' ⊢
  rw [← GradedRingHom.map_directSumDecompose, hx', map_zero]

/-- A graded ring map sends `𝒜₊` into `ℬ₊`. -/
theorem map_irrelevant_le (f : 𝒜 →+*ᵍ ℬ) : 𝒜₊.map f ≤ ℬ₊ := by
  rw [HomogeneousIdeal.map_le_iff_le_comap]
  intro x hx
  change GradedRing.proj ℬ 0 (f x) = 0
  have hx' : GradedRing.proj 𝒜 0 x = 0 := hx
  simp only [GradedRing.proj_apply] at hx' ⊢
  rw [← GradedRingHom.map_directSumDecompose, hx', map_zero]

end Irrelevant

/-! ### The Rees algebra of `Iᵈ` is the `d`-th Veronese subring of the Rees algebra of `I` -/

section ReesVeronese

open Polynomial

variable {R : Type u} [CommRing R] {J K : Ideal R} (d : ℕ) [NeZero d]

theorem coe_decompose_reesGrading (p : reesAlgebra J) (n : ℕ) :
    ((DirectSum.decompose (reesGrading J) p n : reesAlgebra J) : R[X]) =
      monomial n ((p : R[X]).coeff n) := by
  change ((reesDecompose J p n : reesAlgebra J) : R[X]) = _
  rw [reesDecompose_apply, coe_reesComponent]

theorem expand_mem_reesAlgebra (hK : K = J ^ d) (p : reesAlgebra K) :
    expand R d (p : R[X]) ∈ reesAlgebra J := by
  intro n
  rw [coeff_expand (NeZero.pos d)]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left m (NeZero.pos d), pow_mul, ← hK]
    exact p.2 m
  · exact zero_mem _

/-- `p(t) ↦ p(tᵈ)`, from the Rees algebra of `K = Jᵈ` to the Rees algebra of `J`. -/
def reesExpand (hK : K = J ^ d) : reesAlgebra K →+* reesAlgebra J :=
  ((expand R d).toRingHom.comp (reesAlgebra K).val.toRingHom).codRestrict (reesAlgebra J)
    (expand_mem_reesAlgebra d hK)

theorem coe_reesExpand (hK : K = J ^ d) (p : reesAlgebra K) :
    (reesExpand d hK p : R[X]) = expand R d (p : R[X]) :=
  rfl

theorem reesExpand_mem_veroneseSubring (hK : K = J ^ d) (p : reesAlgebra K) :
    reesExpand d hK p ∈ veroneseSubring (reesGrading J) d := by
  intro i hi
  refine Subtype.ext ?_
  rw [coe_decompose_reesGrading, coe_reesExpand, coeff_expand (NeZero.pos d), if_neg hi,
    map_zero]
  rfl

/-- **The Rees algebra of `Iᵈ` as a Veronese subring.** For `K = Jᵈ`, the map `p(t) ↦ p(tᵈ)`
is a graded ring map `⨁ₙ Kⁿ tⁿ → (⨁ₙ Jⁿ tⁿ)^{(d)}` (degree `n` goes to `S^{(d)}_n = Jⁿᵈ tⁿᵈ`). -/
def reesVeronese (hK : K = J ^ d) : reesGrading K →+*ᵍ veronese (reesGrading J) d where
  toRingHom := (reesExpand d hK).codRestrict (veroneseSubring (reesGrading J) d)
    (reesExpand_mem_veroneseSubring d hK)
  map_mem {n p} hp := by
    change reesExpand d hK p ∈ reesGrading J (n * d)
    intro m hm
    rw [coe_reesExpand, coeff_expand (NeZero.pos d)]
    split_ifs with h
    · obtain ⟨j, rfl⟩ := h
      rw [Nat.mul_div_cancel_left j (NeZero.pos d)]
      exact hp j fun hj => hm (by rw [hj, mul_comm])
    · rfl

theorem coe_reesVeronese (hK : K = J ^ d) (p : reesAlgebra K) :
    (((reesVeronese d hK p : veroneseSubring (reesGrading J) d) : reesAlgebra J) : R[X]) =
      expand R d (p : R[X]) :=
  rfl

theorem reesVeronese_injective (hK : K = J ^ d) : Function.Injective (reesVeronese d hK) :=
  fun _ _ h => Subtype.ext <| expand_injective (NeZero.pos d) (congrArg
    (fun x : veroneseSubring (reesGrading J) d => ((x : reesAlgebra J) : R[X])) h)

theorem reesVeronese_surjective (hK : K = J ^ d) : Function.Surjective (reesVeronese d hK) := by
  intro x
  have hx : ∀ n, ¬ d ∣ n → ((x : reesAlgebra J) : R[X]).coeff n = 0 := fun n hn => by
    have h0 := congrArg (fun y : reesAlgebra J => (y : R[X]).coeff n) (x.2 n hn)
    simpa [coe_decompose_reesGrading] using h0
  have hmem : contract d ((x : reesAlgebra J) : R[X]) ∈ reesAlgebra K := fun n => by
    rw [coeff_contract (NeZero.ne d), hK, ← pow_mul, mul_comm]
    exact (x : reesAlgebra J).2 (n * d)
  refine ⟨⟨_, hmem⟩, Subtype.ext (Subtype.ext ?_)⟩
  rw [coe_reesVeronese]
  ext n
  rw [coeff_expand (NeZero.pos d)]
  split_ifs with h
  · rw [coeff_contract (NeZero.ne d), Nat.div_mul_cancel h]
  · exact (hx n h).symm

/-- The inverse `(⨁ₙ Jⁿ tⁿ)^{(d)} → ⨁ₙ Kⁿ tⁿ` of `reesVeronese`, as a graded ring map. -/
def reesVeroneseInv (hK : K = J ^ d) : veronese (reesGrading J) d →+*ᵍ reesGrading K where
  toRingHom := (RingEquiv.ofBijective (reesVeronese d hK)
    ⟨reesVeronese_injective d hK, reesVeronese_surjective d hK⟩).symm.toRingHom
  map_mem {n x} hx := by
    set p := (RingEquiv.ofBijective (reesVeronese d hK)
      ⟨reesVeronese_injective d hK, reesVeronese_surjective d hK⟩).symm x
    have hp : reesVeronese d hK p = x :=
      (RingEquiv.ofBijective (reesVeronese d hK) _).apply_symm_apply x
    change p ∈ reesGrading K n
    intro m hm
    have := (hp ▸ hx : reesVeronese d hK p ∈ veronese (reesGrading J) d n) (m * d)
      fun h => hm (Nat.eq_of_mul_eq_mul_right (NeZero.pos d) h)
    rwa [coe_reesVeronese, coeff_expand_mul (NeZero.pos d)] at this

theorem reesVeronese_reesVeroneseInv (hK : K = J ^ d) (x : veroneseSubring (reesGrading J) d) :
    reesVeronese d hK (reesVeroneseInv d hK x) = x :=
  (RingEquiv.ofBijective (reesVeronese d hK) _).apply_symm_apply x

theorem reesVeroneseInv_reesVeronese (hK : K = J ^ d) (p : reesAlgebra K) :
    reesVeroneseInv d hK (reesVeronese d hK p) = p :=
  (RingEquiv.ofBijective (reesVeronese d hK) _).symm_apply_apply p

theorem irrelevant_le_map_reesVeronese (hK : K = J ^ d) :
    (veronese (reesGrading J) d)₊ ≤ (reesGrading K)₊.map (reesVeronese d hK) :=
  irrelevant_le_map_of_rightInverse _ _ (reesVeronese_reesVeroneseInv d hK)

theorem irrelevant_le_map_reesVeroneseInv (hK : K = J ^ d) :
    (reesGrading K)₊ ≤ (veronese (reesGrading J) d)₊.map (reesVeroneseInv d hK) :=
  irrelevant_le_map_of_rightInverse _ _ (reesVeroneseInv_reesVeronese d hK)

/-- `Proj (⨁ₙ Kⁿ tⁿ) ≅ Proj (⨁ₙ Jⁿ tⁿ)^{(d)}` for `K = Jᵈ`, induced by `reesVeronese`. -/
def projReesVeroneseIso (hK : K = J ^ d) :
    Proj (veronese (reesGrading J) d) ≅ Proj (reesGrading K) where
  hom := Proj.map (reesVeronese d hK) (irrelevant_le_map_reesVeronese d hK)
  inv := Proj.map (reesVeroneseInv d hK) (irrelevant_le_map_reesVeroneseInv d hK)
  hom_inv_id := by
    rw [← Proj.map_comp, ← Proj.map_id]
    congr 1
    exact GradedRingHom.ext fun x => reesVeronese_reesVeroneseInv d hK x
  inv_hom_id := by
    rw [← Proj.map_comp, ← Proj.map_id]
    congr 1
    exact GradedRingHom.ext fun x => reesVeroneseInv_reesVeronese d hK x

end ReesVeronese

/-! ### Blowing up `Iᵈ` -/

namespace QuasicoherentIdealSubsheaf

open Scheme.AffineZariskiSite

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

/-- On a Noetherian scheme, every power `Iᵏ` of a quasi-coherent sheaf of ideals is coherent. -/
theorem isCoherent_pow [IsNoetherian X] (k : ℕ) : IsCoherent (I ^ k).toModules :=
  ArtinReesKernelSheaf.isCoherent_powSmul _ k ArtinReesKernelSheaf.isLocal_top
    (ArtinReesKernelSheaf.isCoherent_top (isCoherent_structureSheafModule X))

theorem idealOn_pow (k : ℕ) (U : X.AffineZariskiSite) :
    ReesAlgebraSheaf.idealOn (quasicoherentIdealSubsheafEquiv (I ^ k)) U =
      ReesAlgebraSheaf.idealOn (quasicoherentIdealSubsheafEquiv I) U ^ k := by
  simp only [ReesAlgebraSheaf.idealOn, quasicoherentIdealSubsheafEquiv_pow,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]

variable (d : ℕ) [NeZero d]

/-- Over an affine open `U`, the identification of `Γ(U, ⨁ₙ (Iᵈ)ⁿ)` with the `d`-th Veronese
subring of `Γ(U, ⨁ₙ Iⁿ)`, `p(t) ↦ p(tᵈ)`. -/
abbrev reesPowVeronese (U : X.AffineZariskiSite) :
    (I ^ d).reesAlgebra.grading U →+*ᵍ veronese (I.reesAlgebra.grading U) d :=
  reesVeronese d (I.idealOn_pow d U)

/-- Over an affine open `U`, `Proj Γ(U, ⨁ₙ Iⁿ) ≅ Proj Γ(U, ⨁ₙ Iⁿ)^{(d)} ≅ Proj Γ(U, ⨁ₙ (Iᵈ)ⁿ)`. -/
def projReesPowIso (U : X.AffineZariskiSite) :
    Proj (I.reesAlgebra.grading U) ≅ Proj ((I ^ d).reesAlgebra.grading U) :=
  Veronese.projIso _ d ≪≫ projReesVeroneseIso d (I.idealOn_pow d U)

theorem irrelevant_le_map_reesPowVeronese (U : X.AffineZariskiSite) :
    (veronese (I.reesAlgebra.grading U) d)₊ ≤
      ((I ^ d).reesAlgebra.grading U)₊.map (I.reesPowVeronese d U) :=
  irrelevant_le_map_reesVeronese d _

theorem projReesPowIso_hom (U : X.AffineZariskiSite) :
    (I.projReesPowIso d U).hom = Veronese.toProj d ≫
      Proj.map (I.reesPowVeronese d U) (I.irrelevant_le_map_reesPowVeronese d U) :=
  rfl

theorem projReesPowIso_hom_naturality {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    Proj.map (I.reesAlgebra.restrict f) (I.reesAlgebra.irrelevant_le f) ≫
        (I.projReesPowIso d V).hom =
      (I.projReesPowIso d U).hom ≫
        Proj.map ((I ^ d).reesAlgebra.restrict f) ((I ^ d).reesAlgebra.irrelevant_le f) := by
  have heq : (I.reesPowVeronese d U).comp ((I ^ d).reesAlgebra.restrict f) =
      (Veronese.veroneseMap d (I.reesAlgebra.restrict f)).comp (I.reesPowVeronese d V) := by
    refine GradedRingHom.ext fun p => Subtype.ext (Subtype.ext ?_)
    exact Polynomial.map_expand.symm
  have hχ := irrelevant_le_map_comp ((I ^ d).reesAlgebra.irrelevant_le f)
    (I.irrelevant_le_map_reesPowVeronese d U)
  rw [heq, HomogeneousIdeal.map_comp] at hχ
  have hφd := hχ.trans (HomogeneousIdeal.map_mono _ (map_irrelevant_le (I.reesPowVeronese d V)))
  rw [projReesPowIso_hom, projReesPowIso_hom,
    reassoc_of% (Veronese.map_comp_toProj d (I.reesAlgebra.restrict f)
      (I.reesAlgebra.irrelevant_le f) hφd), ← Proj.map_comp, Category.assoc, ← Proj.map_comp]
  congr 2
  exact heq.symm

theorem projReesPowIso_hom_projToSpec (U : X.AffineZariskiSite) :
    (I.projReesPowIso d U).hom ≫ (I ^ d).reesAlgebra.projToSpec.app U =
      I.reesAlgebra.projToSpec.app U := by
  change (Veronese.toProj d ≫ Proj.map _ _) ≫ Proj.toSpecZero _ ≫
      Spec.map ((I ^ d).reesAlgebra.toZero U) =
    Proj.toSpecZero _ ≫ Spec.map (I.reesAlgebra.toZero U)
  have h1 := projMap_toSpecZero (I.reesPowVeronese d U) (I.irrelevant_le_map_reesPowVeronese d U)
  have h2 := Veronese.toProj_comp_toSpecZero (𝒜 := I.reesAlgebra.grading U) (d := d)
  rw [Category.assoc]
  erw [reassoc_of% h1]
  erw [reassoc_of% h2]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext r
  refine Subtype.ext ?_
  change Polynomial.expand _ d (Polynomial.C r) = Polynomial.C r
  rw [Polynomial.expand_C]

omit [NeZero d] in
/-- The glued scheme of the relative gluing datum of a quasi-coherent graded algebra exists. -/
theorem hasColimit_relativeGluingData (S : QuasiCoherentGradedAlgebra X) :
    HasColimit S.relativeGluingData.functor := by
  have := Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin
    S.relativeGluingData
  infer_instance

attribute [local instance] hasColimit_relativeGluingData

/-- The natural isomorphism between the gluing data of the blowups along `I` and along `Iᵈ`. -/
def projFunctorPowIso :
    I.reesAlgebra.relativeGluingData.functor ≅
      (I ^ d).reesAlgebra.relativeGluingData.functor :=
  NatIso.ofComponents (fun U => I.projReesPowIso d U) fun f =>
    I.projReesPowIso_hom_naturality d f

set_option backward.isDefEq.respectTransparency.types false in
theorem projFunctorPowIso_hom_natTrans (U : X.AffineZariskiSite) :
    (I.projFunctorPowIso d).hom.app U ≫ (I ^ d).reesAlgebra.relativeGluingData.natTrans.app U =
      I.reesAlgebra.relativeGluingData.natTrans.app U := by
  change (I.projReesPowIso d U).hom ≫
      ((I ^ d).reesAlgebra.projToSpec ≫ (restrictIsoSpec X).inv).app U =
    (I.reesAlgebra.projToSpec ≫ (restrictIsoSpec X).inv).app U
  rw [NatTrans.comp_app, NatTrans.comp_app]
  refine Eq.trans ?_ (congrArg (· ≫ (restrictIsoSpec X).inv.app U)
    (I.projReesPowIso_hom_projToSpec d U))
  exact (Category.assoc _ _ _).symm

variable [IsNoetherian X] (hI : IsCoherent I.toModules)

/-- **Blowups are invariant under powers of the center** (Hartshorne II, Exercise 7.11(a)). For a
coherent sheaf of ideals `I` on a Noetherian scheme `X` and `d > 0`, the blowup of `X` along `Iᵈ`
is canonically isomorphic to the blowup along `I`, over `X`
(`blowupPowIso_hom_blowupProjection`). Over an affine open `U`, it is the isomorphism
`Proj Γ(U, ⨁ₙ (Iᵈ)ⁿ) ≅ Proj Γ(U, ⨁ₙ Iⁿ)^{(d)} ≅ Proj Γ(U, ⨁ₙ Iⁿ)`, the Rees algebra of `Iᵈ` being
the `d`-th Veronese subring of the Rees algebra of `I`. -/
def blowupPowIso (d : ℕ) (hd : 0 < d) : (I ^ d).blowup (I.isCoherent_pow d) ≅ I.blowup hI :=
  haveI : NeZero d := ⟨hd.ne'⟩
  (HasColimit.isoOfNatIso (I.projFunctorPowIso d)).symm

/-- The isomorphism `blowupPowIso` is an isomorphism over `X`: it commutes with the projections of
the two blowups to `X`. -/
theorem blowupPowIso_hom_blowupProjection (d : ℕ) (hd : 0 < d) :
    (I.blowupPowIso hI d hd).hom ≫ I.blowupProjection hI =
      (I ^ d).blowupProjection (I.isCoherent_pow d) := by
  have : NeZero d := ⟨hd.ne'⟩
  change (HasColimit.isoOfNatIso (I.projFunctorPowIso d)).inv ≫
      I.reesAlgebra.relativeGluingData.toBase = (I ^ d).reesAlgebra.relativeGluingData.toBase
  rw [Iso.inv_comp_eq]
  refine colimit.hom_ext fun U => ?_
  rw [HasColimit.isoOfNatIso_ι_hom_assoc, Scheme.Cover.RelativeGluingData.ι_toBase,
    Scheme.Cover.RelativeGluingData.ι_toBase]
  refine (congrArg (· ≫ (Scheme.AffineZariskiSite.directedCover X).f U)
    (I.projFunctorPowIso_hom_natTrans d U)).symm.trans ?_
  exact Category.assoc _ _ _

end QuasicoherentIdealSubsheaf

end Hartshorne
