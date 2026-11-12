/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ReesAlgebraBlowup
import Hartshorne.Scheme.RelativeProjLineBundleTwist

/-!
# Blowing up the product with an invertible sheaf of ideals

Hartshorne, *Algebraic Geometry*, II, Exercise 7.11(b) (p. 171): for a coherent sheaf of ideals
`I` and an invertible sheaf of ideals `L` on a Noetherian scheme `X`, the blowups of `X` along `I`
and along `I · L` are isomorphic; the isomorphism constructed here is canonical and lies over `X`.

## The product of sheaves of ideals

The product `I · J` of two quasi-coherent sheaves of ideals is the quasi-coherent sheaf of ideals
with sections `Γ(U, I) · Γ(U, J)` over the affine opens `U`
(`QuasicoherentIdealSubsheaf.ideal_mul`); on a Noetherian scheme it is coherent
(`QuasicoherentIdealSubsheaf.isCoherent_mul`).

## Proof

Over an affine open `U` on which `L` has a frame, `Γ(U, L) = (f)` for a non-zero-divisor `f` of
`Γ(U, 𝒪_X)` (`ideal_eq_span_frameGen`, `frameGen_mem_nonZeroDivisors`). Then
`Γ(U, I · L)ⁿ = fⁿ Γ(U, I)ⁿ`, and `a tⁿ ↦ fⁿ a tⁿ` is a graded ring isomorphism from the Rees
algebra `⨁ₙ Γ(U, I)ⁿ tⁿ` onto `⨁ₙ Γ(U, I · L)ⁿ tⁿ` (`reesScale`, `reesScale_bijective`). On the
other side, `s ↦ s ⊗ fⁿ` identifies `⨁ₙ Γ(U, I)ⁿ` with the sections of the twist
`(⨁ₙ Iⁿ) · L` of Lemma 7.9. The resulting isomorphisms
`Proj Γ(U, ⨁ₙ (I · L)ⁿ) ≅ Proj Γ(U, (⨁ₙ Iⁿ) · L)` (`projReesMulTwistIso`) do not depend on the
frame (`projReesScaleIso_eq`: changing `f` to `u f` composes with `a tⁿ ↦ uⁿ a tⁿ`, which is the
identity on `Proj`) and are compatible with restriction, so they glue
(`QuasiCoherentGradedAlgebra.framedGlueIso`) to an isomorphism
`Proj_X (⨁ₙ (I · L)ⁿ) ≅ Proj_X ((⨁ₙ Iⁿ) · L)` over `X`. Composing with the isomorphism
`Proj_X ((⨁ₙ Iⁿ) · L) ≅ Proj_X (⨁ₙ Iⁿ)` of Lemma 7.9 gives the result.

## Main definitions and results

* `reesScale`, `projReesScaleIso`: for `K = J · (f)` with `f` a non-zero-divisor, the graded ring
  isomorphism `⨁ₙ Jⁿ tⁿ ≅ ⨁ₙ Kⁿ tⁿ`, `a tⁿ ↦ fⁿ a tⁿ`, and the induced isomorphism of `Proj`s.
* `QuasicoherentIdealSubsheaf.ideal_mul`, `QuasicoherentIdealSubsheaf.isCoherent_mul`: the product
  of quasi-coherent sheaves of ideals.
* `QuasiCoherentGradedAlgebra.framedGlueIso`: compatible isomorphisms `Proj A(U) ≅ Proj B(U)` over
  the affine opens on which an invertible sheaf has a frame glue to `Proj_X A ≅ Proj_X B`.
* `QuasicoherentIdealSubsheaf.blowupMulIso`, `blowupMulIso_hom_blowupProjection`: the isomorphism
  `Bl_{I · L} X ≅ Bl_I X` over `X`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace Hartshorne

/-! ### The Rees algebra of `J · (f)` -/

section ReesScale

variable {R : Type u} [CommRing R] {J K : Ideal R} {f : R}

theorem comp_mem_reesAlgebra (hK : J * Ideal.span {f} ≤ K) (p : reesAlgebra J) :
    (p : R[X]).comp (C f * X) ∈ reesAlgebra K := by
  intro n
  rw [comp_C_mul_X_coeff]
  refine Ideal.pow_right_mono hK n ?_
  rw [mul_pow, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_mul (p.2 n) (Ideal.mem_span_singleton_self _)

/-- `p(t) ↦ p(f t)`, from the Rees algebra of `J` to the Rees algebra of `K ⊇ J · (f)`: it sends
`a tⁿ` to `fⁿ a tⁿ`. -/
def reesScaleRingHom (hK : J * Ideal.span {f} ≤ K) : reesAlgebra J →+* reesAlgebra K :=
  ((compRingHom (C f * X)).comp (reesAlgebra J).val.toRingHom).codRestrict (reesAlgebra K)
    (comp_mem_reesAlgebra hK)

theorem coe_reesScaleRingHom (hK : J * Ideal.span {f} ≤ K) (p : reesAlgebra J) :
    (reesScaleRingHom hK p : R[X]) = (p : R[X]).comp (C f * X) :=
  rfl

/-- **Scaling the Rees algebra by `f`**: the graded ring map `⨁ₙ Jⁿ tⁿ → ⨁ₙ Kⁿ tⁿ`,
`a tⁿ ↦ fⁿ a tⁿ`, for `J · (f) ⊆ K`. -/
def reesScale (hK : J * Ideal.span {f} ≤ K) : reesGrading J →+*ᵍ reesGrading K where
  toRingHom := reesScaleRingHom hK
  map_mem {n p} hp m hm := by
    rw [coe_reesScaleRingHom, comp_C_mul_X_coeff, hp m hm, zero_mul]

theorem coe_reesScale (hK : J * Ideal.span {f} ≤ K) (p : reesAlgebra J) :
    (reesScale hK p : R[X]) = (p : R[X]).comp (C f * X) :=
  rfl

theorem reesScale_injective (hK : J * Ideal.span {f} ≤ K) (hf : f ∈ nonZeroDivisors R) :
    Function.Injective (reesScale hK) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  refine Subtype.ext ((comp_C_mul_X_eq_zero_iff hf).1 ?_)
  exact congrArg Subtype.val hp

theorem reesScale_surjective (hK : K = J * Ideal.span {f}) (hf : f ∈ nonZeroDivisors R) :
    Function.Surjective (reesScale hK.ge) := by
  classical
  subst hK
  intro q
  have h : ∀ n, ∃ a ∈ J ^ n, a * f ^ n = (q : R[X]).coeff n := fun n => by
    have hq := q.2 n
    rw [mul_pow, Ideal.span_singleton_pow] at hq
    exact Ideal.mem_mul_span_singleton.1 hq
  choose a ha hfa using h
  let p : R[X] := ∑ n ∈ (q : R[X]).support, monomial n (a n)
  have hp : ∀ n, p.coeff n = a n := fun n => by
    simp only [p, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq',
      mem_support_iff]
    split_ifs with hn
    · rfl
    · rw [not_not, ← hfa n] at hn
      exact ((mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hf n)).1 hn).symm
  refine ⟨⟨p, fun n => by rw [hp]; exact ha n⟩, Subtype.ext ?_⟩
  ext n
  rw [coe_reesScale, comp_C_mul_X_coeff]
  change p.coeff n * f ^ n = _
  rw [hp, hfa]

theorem reesScale_bijective (hK : K = J * Ideal.span {f}) (hf : f ∈ nonZeroDivisors R) :
    Function.Bijective (reesScale hK.ge) :=
  ⟨reesScale_injective hK.ge hf, reesScale_surjective hK hf⟩

/-- `Proj (⨁ₙ Kⁿ tⁿ) ≅ Proj (⨁ₙ Jⁿ tⁿ)` for `K = J · (f)` with `f` a non-zero-divisor, induced
by `a tⁿ ↦ fⁿ a tⁿ`. -/
def projReesScaleIso (hK : K = J * Ideal.span {f}) (hf : f ∈ nonZeroDivisors R) :
    Proj (reesGrading K) ≅ Proj (reesGrading J) :=
  projIsoOfBijective (reesScale hK.ge) (reesScale_bijective hK hf)

theorem projReesScaleIso_hom (hK : K = J * Ideal.span {f}) (hf : f ∈ nonZeroDivisors R) :
    ∃ h, (projReesScaleIso hK hf).hom = Proj.map (reesScale hK.ge) h :=
  ⟨_, projIsoOfBijective_hom _ _⟩

/-- Replacing `f` by `u f` composes `a tⁿ ↦ fⁿ a tⁿ` with `a tⁿ ↦ uⁿ a tⁿ`. -/
theorem reesScale_mul_left (hK : J * Ideal.span {f} ≤ K) (u : R)
    (hK' : J * Ideal.span {u * f} ≤ K) :
    reesScale hK' =
      (reesScale hK).comp
        (SegreProduct.scale (reesGrading J) (algebraMap_mem_reesGrading_zero J) u) := by
  have := SegreProduct.ringHom_ext_of_homogeneous (𝒮 := reesGrading J)
    (f := (reesScale hK').toRingHom)
    (g := ((reesScale hK).comp (SegreProduct.scale (reesGrading J)
      (algebraMap_mem_reesGrading_zero J) u)).toRingHom) fun d s hs => by
      refine Subtype.ext ?_
      change (reesScale hK' s : R[X]) = (reesScale hK (SegreProduct.scale (reesGrading J)
        (algebraMap_mem_reesGrading_zero J) u s) : R[X])
      rw [SegreProduct.scale_of_mem _ _ u hs, coe_reesScale, coe_reesScale, Subalgebra.coe_smul]
      ext m
      rw [comp_C_mul_X_coeff, comp_C_mul_X_coeff, coeff_smul, smul_eq_mul]
      by_cases hm : m = d
      · subst hm
        ring
      · rw [hs m hm]
        ring
  exact GradedRingHom.ext fun p => congr($this p)

private theorem projMap_congr {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A]
    [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
    [GradedRing 𝒜] [GradedRing ℬ] {φ ψ : 𝒜 →+*ᵍ ℬ} (e : φ = ψ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ) :
    Proj.map φ hφ = Proj.map ψ hψ := by
  subst e
  rfl

/-- **Independence of the generator**: two non-zero-divisors generating the same principal ideal
give the same isomorphism `Proj (⨁ₙ Kⁿ tⁿ) ≅ Proj (⨁ₙ Jⁿ tⁿ)`. -/
theorem projReesScaleIso_eq {f' : R} (hK : K = J * Ideal.span {f}) (hf : f ∈ nonZeroDivisors R)
    (hK' : K = J * Ideal.span {f'}) (hf' : f' ∈ nonZeroDivisors R)
    (hspan : Ideal.span {f'} = Ideal.span {f}) :
    projReesScaleIso hK' hf' = projReesScaleIso hK hf := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 (hspan ▸ Ideal.mem_span_singleton_self f')
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hspan ▸ Ideal.mem_span_singleton_self f)
  have hba : b * a = 1 := by
    have : (b * a - 1) * f = 0 := by rw [sub_mul, one_mul, mul_assoc, hb, sub_self]
    exact sub_eq_zero.1 ((mul_right_mem_nonZeroDivisors_eq_zero_iff hf).1 this)
  have hu : IsUnit a := IsUnit.of_mul_eq_one_right b hba
  refine Iso.ext ?_
  obtain ⟨h₁, e₁⟩ := projReesScaleIso_hom hK' hf'
  obtain ⟨h₂, e₂⟩ := projReesScaleIso_hom hK hf
  rw [e₁, e₂]
  refine (projMap_congr (reesScale_mul_left hK.ge a hK'.ge) _
    (HomogeneousIdeal.irrelevant_le_map_comp (SegreProduct.irrelevant_le_scale _ _ hu) h₂)).trans ?_
  rw [Proj.map_comp _ _ (SegreProduct.irrelevant_le_scale _ _ hu) h₂,
    SegreProduct.projMap_scale _ _ hu, Category.comp_id]

/-- `a tⁿ ↦ fⁿ a tⁿ` commutes with base change of the coefficients. -/
theorem reesMap_comp_reesScaleRingHom {R' : Type u} [CommRing R'] {J' K' : Ideal R'}
    (φ : R →+* R') (hJ : J.map φ ≤ J') (hK : K.map φ ≤ K') (hKf : J * Ideal.span {f} ≤ K)
    (hKf' : J' * Ideal.span {φ f} ≤ K') :
    (reesMap φ hK).comp (reesScaleRingHom hKf) = (reesScaleRingHom hKf').comp (reesMap φ hJ) := by
  ext p : 1
  refine Subtype.ext ?_
  change ((p : R[X]).comp (C f * X)).map φ = ((p : R[X]).map φ).comp (C (φ f) * X)
  rw [Polynomial.map_comp, Polynomial.map_mul, map_C, map_X]

end ReesScale

/-! ### The product of two quasi-coherent sheaves of ideals -/

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}}

/-- **The product `I · J` of two quasi-coherent sheaves of ideals**: the quasi-coherent sheaf of
ideals whose sections over every affine open `U` are `Γ(U, I) · Γ(U, J)`. -/
instance : Mul (QuasicoherentIdealSubsheaf X) where
  mul I J := quasicoherentIdealSubsheafEquiv.symm
    (quasicoherentIdealSubsheafEquiv I * quasicoherentIdealSubsheafEquiv J)

/-- Over every affine open `U`, `Γ(U, I · J) = Γ(U, I) · Γ(U, J)`. -/
theorem ideal_mul (I J : QuasicoherentIdealSubsheaf X) (U : X.affineOpens) :
    (I * J).ideal U = I.ideal U * J.ideal U :=
  quasicoherentIdealSubsheafEquiv_symm_ideal _ U

/-- On a Noetherian scheme, the product `I · J` of quasi-coherent sheaves of ideals is coherent. -/
theorem isCoherent_mul [IsNoetherian X] (I J : QuasicoherentIdealSubsheaf X) :
    IsCoherent (I * J).toModules :=
  ArtinReesKernelSheaf.isCoherent_powSmul _ 1 ArtinReesKernelSheaf.isLocal_top
    (ArtinReesKernelSheaf.isCoherent_top (isCoherent_structureSheafModule X))

/-! ### Frames of an invertible sheaf of ideals -/

variable {L : QuasicoherentIdealSubsheaf X} {U : X.Opens}
  {e : ULift.{u} (Fin 1) → Γ(L.toModules, U)}

theorem localFrameMap_refl_apply (a : ULift.{u} (Fin 1) → Γ(X, U)) :
    Ringed.localFrameMap (R := X.sheaf) L.toModules e (le_refl U) a = a default • e default := by
  refine (Ringed.localFrameMap_apply (R := X.sheaf) L.toModules e (le_refl U) a).trans ?_
  rw [Fintype.sum_unique]
  congr 1
  exact congr($((L.toModules : SheafOfModules _).val.presheaf.map_id (Opposite.op U)) (e default))

theorem exists_smul_frame (he : Ringed.IsLocalFrame (R := X.sheaf) L.toModules U e)
    (x : Γ(L.toModules, U)) : ∃ r : Γ(X, U), r • e default = x := by
  obtain ⟨a, ha⟩ := (he U le_rfl).2 x
  exact ⟨a default, (localFrameMap_refl_apply a).symm.trans ha⟩

theorem smul_frame_injective (he : Ringed.IsLocalFrame (R := X.sheaf) L.toModules U e) :
    Function.Injective fun r : Γ(X, U) => r • e default := fun r s h =>
  congrFun ((he U le_rfl).1 (a₁ := fun _ => r) (a₂ := fun _ => s)
    ((localFrameMap_refl_apply (fun _ => r)).trans
      (h.trans (localFrameMap_refl_apply (fun _ => s)).symm))) default

variable (e) in
/-- The section `f ∈ Γ(U, L) ⊆ Γ(U, 𝒪_X)` of a frame `e` of a sheaf of ideals `L` over `U`. -/
abbrev frameGen : Γ(X, U) :=
  (e default).1

/-- A frame `f` of a sheaf of ideals `L` over `U` generates `Γ(U, L)`. -/
theorem ideal_eq_span_frameGen (he : Ringed.IsLocalFrame (R := X.sheaf) L.toModules U e) :
    L.ideal U = Ideal.span {frameGen e} := by
  refine le_antisymm (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).2 (e default).2)
  obtain ⟨r, hr⟩ := exists_smul_frame he ⟨x, hx⟩
  exact Ideal.mem_span_singleton'.2 ⟨r, congrArg Subtype.val hr⟩

/-- A frame `f` of a sheaf of ideals over `U` is a non-zero-divisor of `Γ(U, 𝒪_X)`. -/
theorem frameGen_mem_nonZeroDivisors (he : Ringed.IsLocalFrame (R := X.sheaf) L.toModules U e) :
    frameGen e ∈ nonZeroDivisors Γ(X, U) := by
  refine mem_nonZeroDivisors_iff_right.2 fun r hr => smul_frame_injective he ?_
  refine Subtype.ext ?_
  change r * frameGen e = (0 : Γ(X, U)) * frameGen e
  rw [hr, zero_mul]

/-! ### The local isomorphisms `Proj Γ(U, ⨁ₙ (I · L)ⁿ) ≅ Proj Γ(U, ⨁ₙ Iⁿ)` -/

variable (I L : QuasicoherentIdealSubsheaf X)

theorem idealOn_mul_eq {U : X.AffineZariskiSite} {e : ULift.{u} (Fin 1) → Γ(L.toModules, U.1)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) L.toModules U.1 e) :
    ReesAlgebraSheaf.idealOn (quasicoherentIdealSubsheafEquiv (I * L)) U =
      ReesAlgebraSheaf.idealOn (quasicoherentIdealSubsheafEquiv I) U * Ideal.span {frameGen e} :=
  (ideal_mul I L ⟨U.1, U.2⟩).trans (congrArg _ (ideal_eq_span_frameGen he))

/-- Over an affine open `U` on which the invertible sheaf of ideals `L` has a frame `f`,
`Proj Γ(U, ⨁ₙ (I · L)ⁿ) ≅ Proj Γ(U, ⨁ₙ Iⁿ)`, induced by `a tⁿ ↦ fⁿ a tⁿ`. -/
def projReesMulIsoOfFrame {U : X.AffineZariskiSite} {e : ULift.{u} (Fin 1) → Γ(L.toModules, U.1)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) L.toModules U.1 e) :
    Proj ((I * L).reesAlgebra.grading U) ≅ Proj (I.reesAlgebra.grading U) :=
  projReesScaleIso (I.idealOn_mul_eq L he) (frameGen_mem_nonZeroDivisors he)

/-- **Independence of the frame**: two frames of `L` over `U` give the same isomorphism
`Proj Γ(U, ⨁ₙ (I · L)ⁿ) ≅ Proj Γ(U, ⨁ₙ Iⁿ)`. -/
theorem projReesMulIsoOfFrame_eq {U : X.AffineZariskiSite}
    {e e' : ULift.{u} (Fin 1) → Γ(L.toModules, U.1)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) L.toModules U.1 e)
    (he' : Ringed.IsLocalFrame (R := X.sheaf) L.toModules U.1 e') :
    I.projReesMulIsoOfFrame L he' = I.projReesMulIsoOfFrame L he :=
  projReesScaleIso_eq _ _ _ _ ((ideal_eq_span_frameGen he').symm.trans (ideal_eq_span_frameGen he))

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the local isomorphism** along a basic open inclusion `U ⊆ V`, with the
restricted frame on `U`. -/
theorem projReesMulIsoOfFrame_naturality {U V : X.AffineZariskiSite} (g : U ⟶ V)
    {e : ULift.{u} (Fin 1) → Γ(L.toModules, V.1)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) L.toModules V.1 e) :
    Proj.map ((I * L).reesAlgebra.restrict g) ((I * L).reesAlgebra.irrelevant_le g) ≫
        (I.projReesMulIsoOfFrame L he).hom =
      (I.projReesMulIsoOfFrame L (QuasiCoherentGradedAlgebra.isLocalFrame_restrictFrame g he)).hom ≫
        Proj.map (I.reesAlgebra.restrict g) (I.reesAlgebra.irrelevant_le g) := by
  obtain ⟨h₁, e₁⟩ := projReesScaleIso_hom (I.idealOn_mul_eq L he) (frameGen_mem_nonZeroDivisors he)
  obtain ⟨h₂, e₂⟩ := projReesScaleIso_hom
    (I.idealOn_mul_eq L (QuasiCoherentGradedAlgebra.isLocalFrame_restrictFrame g he))
    (frameGen_mem_nonZeroDivisors (QuasiCoherentGradedAlgebra.isLocalFrame_restrictFrame g he))
  rw [projReesMulIsoOfFrame, projReesMulIsoOfFrame, e₁, e₂, ← Proj.map_comp, ← Proj.map_comp]
  refine projMap_congr (GradedRingHom.ext fun p => ?_) _ _
  exact congr($(reesMap_comp_reesScaleRingHom
    (X.presheaf.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map g).op).hom
    (ReesAlgebraSheaf.map_idealOn _ g).le (ReesAlgebraSheaf.map_idealOn _ g).le
    (I.idealOn_mul_eq L he).ge
    (I.idealOn_mul_eq L (QuasiCoherentGradedAlgebra.isLocalFrame_restrictFrame g he)).ge) p)

set_option backward.isDefEq.respectTransparency false in
/-- The local isomorphism lies over `Spec Γ(U, 𝒪_X)`. -/
theorem projReesMulIsoOfFrame_hom_toSpec {U : X.AffineZariskiSite}
    {e : ULift.{u} (Fin 1) → Γ(L.toModules, U.1)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) L.toModules U.1 e) :
    (I.projReesMulIsoOfFrame L he).hom ≫ Proj.toSpecZero (I.reesAlgebra.grading U) ≫
        Spec.map (I.reesAlgebra.toZero U) =
      Proj.toSpecZero ((I * L).reesAlgebra.grading U) ≫
        Spec.map ((I * L).reesAlgebra.toZero U) := by
  obtain ⟨h, e₁⟩ := projReesScaleIso_hom (I.idealOn_mul_eq L he) (frameGen_mem_nonZeroDivisors he)
  have h₁ := projMap_toSpecZero (reesScale (I.idealOn_mul_eq L he).ge) h
  rw [projReesMulIsoOfFrame, e₁]
  erw [reassoc_of% h₁]
  rw [← Spec.map_comp]
  congr 2
  ext r n
  change ((C r).comp (C (frameGen e) * Polynomial.X)).coeff n = (C r).coeff n
  rw [C_comp]

end QuasicoherentIdealSubsheaf

/-! ### Gluing local isomorphisms over the affine opens on which an invertible sheaf has a frame -/

namespace QuasiCoherentGradedAlgebra

variable {X : Scheme.{u}} {M : X.Modules} (hM : M.IsInvertible) {A B : QuasiCoherentGradedAlgebra X}
  (φ : ∀ U : (framedAffines M).FullSubcategory, Proj (A.grading U.obj) ≅ Proj (B.grading U.obj))
  (hφ : ∀ {U V : (framedAffines M).FullSubcategory} (f : U ⟶ V),
    Proj.map (A.restrict f.hom) (A.irrelevant_le f.hom) ≫ (φ V).hom =
      (φ U).hom ≫ Proj.map (B.restrict f.hom) (B.irrelevant_le f.hom))

include hφ in
set_option backward.isDefEq.respectTransparency false in
theorem framedGlue_hom_compat {U V : (framedCover hM A).I₀} (f : U ⟶ V) :
    (framedCover hM A).trans f ≫ (φ V).hom ≫ B.projι V.obj = (φ U).hom ≫ B.projι U.obj := by
  rw [framedCover_trans, ← Category.assoc, hφ, Category.assoc, restrict_projι]

include hφ in
set_option backward.isDefEq.respectTransparency false in
theorem framedGlue_inv_compat {U V : (framedCover hM B).I₀} (f : U ⟶ V) :
    (framedCover hM B).trans f ≫ (φ V).inv ≫ A.projι V.obj = (φ U).inv ≫ A.projι U.obj := by
  rw [framedCover_trans, ← Category.assoc, ← restrict_projι _ f.hom, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, hφ, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `Proj_X A ⟶ Proj_X B` glued from isomorphisms `Proj A(U) ≅ Proj B(U)` over the
affine opens `U` on which `M` has a frame, compatible with restriction. -/
noncomputable def framedGlueHom : A.relProj ⟶ B.relProj :=
  (framedCover hM A).glueMorphismsOfLocallyDirected (fun U => (φ U).hom ≫ B.projι U.obj)
    (framedGlue_hom_compat hM φ hφ)

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `Proj_X B ⟶ Proj_X A` glued from the inverses of the local isomorphisms. -/
noncomputable def framedGlueInv : B.relProj ⟶ A.relProj :=
  (framedCover hM B).glueMorphismsOfLocallyDirected (fun U => (φ U).inv ≫ A.projι U.obj)
    (framedGlue_inv_compat hM φ hφ)

set_option backward.isDefEq.respectTransparency false in
theorem projι_framedGlueHom (U : (framedAffines M).FullSubcategory) :
    A.projι U.obj ≫ framedGlueHom hM φ hφ = (φ U).hom ≫ B.projι U.obj :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (framedCover hM A) _
    (framedGlue_hom_compat hM φ hφ) U

set_option backward.isDefEq.respectTransparency false in
theorem projι_framedGlueInv (U : (framedAffines M).FullSubcategory) :
    B.projι U.obj ≫ framedGlueInv hM φ hφ = (φ U).inv ≫ A.projι U.obj :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (framedCover hM B) _
    (framedGlue_inv_compat hM φ hφ) U

set_option backward.isDefEq.respectTransparency false in
/-- **Gluing over the framed affine opens**: isomorphisms `Proj A(U) ≅ Proj B(U)` over the affine
opens `U` on which the invertible sheaf `M` has a frame, compatible with restriction, glue to an
isomorphism `Proj_X A ≅ Proj_X B`. -/
noncomputable def framedGlueIso : A.relProj ≅ B.relProj where
  hom := framedGlueHom hM φ hφ
  inv := framedGlueInv hM φ hφ
  hom_inv_id := (framedCover hM A).hom_ext _ _ fun U => by
    change A.projι U.obj ≫ _ = A.projι U.obj ≫ _
    rw [← Category.assoc, projι_framedGlueHom, Category.assoc, projι_framedGlueInv,
      Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := (framedCover hM B).hom_ext _ _ fun U => by
    change B.projι U.obj ≫ _ = B.projι U.obj ≫ _
    rw [← Category.assoc, projι_framedGlueInv, Category.assoc, projι_framedGlueHom,
      Iso.inv_hom_id_assoc, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- If the local isomorphisms lie over `Spec Γ(U, 𝒪_X)`, the glued isomorphism lies over `X`. -/
theorem framedGlueIso_hom_relProjToBase
    (hbase : ∀ U : (framedAffines M).FullSubcategory,
      (φ U).hom ≫ Proj.toSpecZero (B.grading U.obj) ≫ Spec.map (B.toZero U.obj) =
        Proj.toSpecZero (A.grading U.obj) ≫ Spec.map (A.toZero U.obj)) :
    (framedGlueIso hM φ hφ).hom ≫ B.relProjToBase = A.relProjToBase :=
  (framedCover hM A).hom_ext _ _ fun U => by
    change A.projι U.obj ≫ framedGlueHom hM φ hφ ≫ _ = A.projι U.obj ≫ _
    rw [← Category.assoc, projι_framedGlueHom, Category.assoc, projι_relProjToBase,
      projι_relProjToBase, projToOpen_ι, projToOpen_ι, ← Category.assoc, ← Category.assoc,
      ← Category.assoc, Category.assoc _ (Proj.toSpecZero _), hbase, Category.assoc]

end QuasiCoherentGradedAlgebra

/-! ### Blowing up `I · L` -/

namespace QuasicoherentIdealSubsheaf

open QuasiCoherentGradedAlgebra

variable {X : Scheme.{u}} (I L : QuasicoherentIdealSubsheaf X) (hL : L.toModules.IsInvertible)

/-- Over an affine open `U` on which `L` has a frame `f`, the isomorphism
`Proj Γ(U, ⨁ₙ (I · L)ⁿ) ≅ Proj Γ(U, ⨁ₙ Iⁿ) ≅ Proj Γ(U, (⨁ₙ Iⁿ) · L)`: the first map is induced by
`a tⁿ ↦ fⁿ a tⁿ`, the second is the inverse of the local isomorphism `s ↦ s ⊗ fⁿ` of Lemma 7.9. -/
def projReesMulTwistIso (U : (framedAffines L.toModules).FullSubcategory) :
    Proj ((I * L).reesAlgebra.grading U.obj) ≅
      Proj ((I.reesAlgebra.lineBundleTwist L.toModules hL).grading U.obj) :=
  I.projReesMulIsoOfFrame L U.property.choose_spec ≪≫ (I.reesAlgebra.framedIso (hL := hL) U).symm

theorem projReesMulTwistIso_naturality {U V : (framedAffines L.toModules).FullSubcategory}
    (g : U ⟶ V) :
    Proj.map ((I * L).reesAlgebra.restrict g.hom) ((I * L).reesAlgebra.irrelevant_le g.hom) ≫
        (I.projReesMulTwistIso L hL V).hom =
      (I.projReesMulTwistIso L hL U).hom ≫
        Proj.map ((I.reesAlgebra.lineBundleTwist L.toModules hL).restrict g.hom)
          ((I.reesAlgebra.lineBundleTwist L.toModules hL).irrelevant_le g.hom) := by
  have h₁ := I.reesAlgebra.framedIso_naturality (hL := hL) g
  have h₂ : Proj.map (I.reesAlgebra.restrict g.hom) (I.reesAlgebra.irrelevant_le g.hom) ≫
      (I.reesAlgebra.framedIso (hL := hL) V).inv =
        (I.reesAlgebra.framedIso (hL := hL) U).inv ≫
          Proj.map ((I.reesAlgebra.lineBundleTwist L.toModules hL).restrict g.hom)
            ((I.reesAlgebra.lineBundleTwist L.toModules hL).irrelevant_le g.hom) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h₁, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [projReesMulTwistIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% (I.projReesMulIsoOfFrame_naturality L g.hom V.property.choose_spec),
    I.projReesMulIsoOfFrame_eq L U.property.choose_spec
      (isLocalFrame_restrictFrame g.hom V.property.choose_spec), h₂]

set_option backward.isDefEq.respectTransparency false in
theorem projReesMulTwistIso_hom_toSpec (U : (framedAffines L.toModules).FullSubcategory) :
    (I.projReesMulTwistIso L hL U).hom ≫
        Proj.toSpecZero ((I.reesAlgebra.lineBundleTwist L.toModules hL).grading U.obj) ≫
          Spec.map ((I.reesAlgebra.lineBundleTwist L.toModules hL).toZero U.obj) =
      Proj.toSpecZero ((I * L).reesAlgebra.grading U.obj) ≫
        Spec.map ((I * L).reesAlgebra.toZero U.obj) := by
  have h₁ := I.reesAlgebra.framedIso_hom_toSpec (hL := hL) U
  rw [projReesMulTwistIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← h₁,
    Iso.inv_hom_id_assoc, projReesMulIsoOfFrame_hom_toSpec]

variable [IsNoetherian X] (hI : IsCoherent I.toModules)

/-- **Blowups are invariant under invertible factors** (Hartshorne II, Exercise 7.11(b): the two
blowups are isomorphic). For a coherent sheaf of ideals `I` and an invertible sheaf of ideals `L` on
a Noetherian scheme `X`, the blowup of `X` along `I · L` is canonically isomorphic to the blowup
along `I`, over `X`
(`blowupMulIso_hom_blowupProjection`). It is the composite
`Proj_X (⨁ₙ (I · L)ⁿ) ≅ Proj_X ((⨁ₙ Iⁿ) · L) ≅ Proj_X (⨁ₙ Iⁿ)`: the first isomorphism is glued
from the identifications `Γ(U, ⨁ₙ (I · L)ⁿ) ≅ Γ(U, ⨁ₙ Iⁿ) ≅ Γ(U, (⨁ₙ Iⁿ) · L)` over the affine opens
`U` on which `L` is generated by a non-zero-divisor `f`, `fⁿ a tⁿ ↤ a tⁿ ↦ a ⊗ fⁿ`, and the second
is the isomorphism of Lemma 7.9. -/
def blowupMulIso : (I * L).blowup (isCoherent_mul I L) ≅ I.blowup hI :=
  framedGlueIso hL (I.projReesMulTwistIso L hL) (I.projReesMulTwistIso_naturality L hL) ≪≫
    I.reesAlgebra.lineBundleTwistIso hL

/-- The isomorphism `blowupMulIso` is an isomorphism over `X`: it commutes with the projections of
the two blowups to `X`. -/
theorem blowupMulIso_hom_blowupProjection :
    (I.blowupMulIso L hL hI).hom ≫ I.blowupProjection hI =
      (I * L).blowupProjection (isCoherent_mul I L) := by
  change (framedGlueIso hL (I.projReesMulTwistIso L hL) (I.projReesMulTwistIso_naturality L hL) ≪≫
      I.reesAlgebra.lineBundleTwistIso hL).hom ≫ I.reesAlgebra.relProjToBase =
    (I * L).reesAlgebra.relProjToBase
  rw [Iso.trans_hom, Category.assoc, lineBundleTwistIso_hom_relProjToBase,
    framedGlueIso_hom_relProjToBase _ _ _ (I.projReesMulTwistIso_hom_toSpec L hL)]

end QuasicoherentIdealSubsheaf

end Hartshorne
