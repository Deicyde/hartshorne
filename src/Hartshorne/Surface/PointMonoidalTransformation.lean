/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.SurfaceCurveConvention
import Hartshorne.Scheme.BlowupVariety
import Hartshorne.Scheme.BlowupExceptionalIdeal
import Hartshorne.Cohomology.SerreAffinenessCriterion

/-!
# The monoidal transformation at a point

Hartshorne, *Algebraic Geometry*, V.3, definition and notation (p. 386).

Let `X` be a surface (in the sense of Chapter V) and `P` a closed point of `X`. The *monoidal
transformation with center `P`* is the blowing-up `π : X̃ = Bl_P(X) ⟶ X` of `X` along the ideal
sheaf `𝔪_P` of the reduced closed point `P`. Its *exceptional divisor* is `E = π⁻¹(P)`, the
effective Cartier divisor on `X̃` whose ideal sheaf is the inverse image ideal sheaf
`π⁻¹𝔪_P · 𝒪_{X̃}`; its support is the set-theoretic fibre `π⁻¹(P)`. The morphism `π` restricts to
an isomorphism `X̃ - E ≅ X - P`.

Since `𝔪_P` is a nonzero coherent sheaf of ideals on the projective variety `X` (nonzero because
`X` has dimension two, so `X - P` is nonempty), `X̃` is integral and projective over `k`, and `π` is
projective and surjective (Proposition II.7.16). That `X̃` is again a surface is a separate result.

## Main definitions and results

* `Hartshorne.Surface.pointIdeal`: the ideal sheaf `𝔪_P` of a closed point.
* `Hartshorne.Surface.pointBlowup`, `Hartshorne.Surface.pointBlowupProjection`: the monoidal
  transformation `π : X̃ ⟶ X` with center `P`.
* `Hartshorne.Surface.pointBlowupExceptional`: the exceptional divisor `E = π⁻¹(P)`.
* `Hartshorne.Surface.pointCompl`, `Hartshorne.Surface.pointBlowupExceptionalCompl`: the open
  subschemes `X - P` and `X̃ - E`.
* `Hartshorne.Surface.pointBlowupIsoOffCenter`: the isomorphism `X̃ - E ≅ X - P` induced by `π`.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hartshorne

noncomputable section

namespace Surface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Surface k) (P : S.Point)

/-! ### The ideal sheaf of a closed point -/

/-- **The ideal sheaf `𝔪_P` of a closed point** `P`: the sheaf of functions vanishing at `P`, the
ideal sheaf of `P` with its reduced induced structure. -/
def pointIdeal : QuasicoherentIdealSubsheaf S.X :=
  quasicoherentIdealSubsheafEquiv.symm (Scheme.IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩)

theorem quasicoherentIdealSubsheafEquiv_pointIdeal :
    quasicoherentIdealSubsheafEquiv (S.pointIdeal P) =
      Scheme.IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩ :=
  Equiv.apply_symm_apply _ _

/-- The ideal sheaf `𝔪_P` is coherent (the surface is Noetherian). -/
theorem isCoherent_pointIdeal : IsCoherent (S.pointIdeal P).toModules :=
  SerreAffineness.isCoherent_toModules _

/-- The closed subscheme cut out by `𝔪_P` is supported exactly at `P`. -/
theorem range_subschemeι_pointIdeal :
    Set.range (quasicoherentIdealSubsheafEquiv (S.pointIdeal P)).subschemeι = {P.1} := by
  rw [quasicoherentIdealSubsheafEquiv_pointIdeal, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- A surface has a point other than `P`: a one-point space has dimension zero, not two. -/
theorem exists_ne_point : ∃ x : S.X, x ≠ P.1 := by
  by_contra! h
  have : Subsingleton S.X := ⟨fun a b => (h a).trans (h b).symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology S.X
  rw [S.dim_eq] at h0
  exact absurd h0 (by decide)

/-- The ideal sheaf `𝔪_P` is nonzero: it is the unit ideal on an affine open avoiding `P`, and
such opens exist because the surface has dimension two. -/
theorem exists_pointIdeal_ne_bot : ∃ U : S.X.Opens, (S.pointIdeal P).ideal U ≠ ⊥ := by
  obtain ⟨x, hx⟩ := S.exists_ne_point P
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVP⟩ := S.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ({P.1}ᶜ : Set S.X) from hx) P.2.isOpen_compl
  refine ⟨V, ?_⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have h := quasicoherentIdealSubsheafEquiv_symm_ideal
    (Scheme.IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩) ⟨V, hV⟩
  change (S.pointIdeal P).ideal V = _ at h
  rw [h, Scheme.IdealSheafData.vanishingIdeal_ideal]
  refine fun hbot => one_ne_zero ((Submodule.eq_bot_iff _).1 hbot 1 ?_)
  rw [PrimeSpectrum.mem_vanishingIdeal]
  intro y hy
  exact absurd hy (hVP ((IsAffineOpen.range_fromSpec hV).subset ⟨y, rfl⟩))

/-! ### The monoidal transformation -/

/-- **The monoidal transformation with center `P`** (Hartshorne V.3, p. 386): the blowing-up
`X̃ = Bl_P(X)` of the surface `X` along the ideal sheaf `𝔪_P` of the closed point `P`. -/
def pointBlowup : Scheme.{u} :=
  (S.pointIdeal P).blowup (S.isCoherent_pointIdeal P)

/-- **The projection `π : X̃ = Bl_P(X) ⟶ X`** of the monoidal transformation with center `P`. -/
def pointBlowupProjection : S.pointBlowup P ⟶ S.X :=
  (S.pointIdeal P).blowupProjection (S.isCoherent_pointIdeal P)

/-- The monoidal transformation `X̃ = Bl_P(X)` is integral (Proposition II.7.16). -/
instance isIntegral_pointBlowup : IsIntegral (S.pointBlowup P) :=
  (S.pointIdeal P).isIntegral_blowup (S.isCoherent_pointIdeal P) (S.exists_pointIdeal_ne_bot P)

/-- The monoidal transformation is a projective variety over `k` and its projection is
projective and surjective (Proposition II.7.16): `π : X̃ ⟶ X` is projective and surjective, and
`X̃ ⟶ X ⟶ Spec k` is projective. -/
theorem pointBlowup_projective :
    Projective (S.pointBlowupProjection P) ∧ Surjective (S.pointBlowupProjection P) ∧
      Projective (S.pointBlowupProjection P ≫ S.hom) := by
  obtain ⟨-, -, -, hsurj, -, hproj⟩ := QuasicoherentIdealSubsheaf.blowup_variety S.hom
    S.finiteType (S.pointIdeal P) (S.isCoherent_pointIdeal P) (S.exists_pointIdeal_ne_bot P)
  exact ⟨(hproj S.projective).1, hsurj, (hproj S.projective).2⟩

/-! ### The exceptional divisor -/

/-- **The exceptional divisor `E = π⁻¹(P)`** of the monoidal transformation: the effective
Cartier divisor on `X̃` whose ideal sheaf is the inverse image ideal sheaf `π⁻¹𝔪_P · 𝒪_{X̃}`
(`idealSheafData_pointBlowupExceptional`). -/
def pointBlowupExceptional : (S.pointBlowup P).CartierDivisor :=
  (S.pointIdeal P).exceptionalDivisor (S.isCoherent_pointIdeal P)

theorem pointBlowupExceptional_isEffective : (S.pointBlowupExceptional P).IsEffective :=
  (S.pointIdeal P).exceptionalDivisor_isEffective (S.isCoherent_pointIdeal P)

/-- `E = π⁻¹(P)` scheme-theoretically: the ideal sheaf of `E` is the inverse image ideal sheaf
of `𝔪_P`, the ideal sheaf of the closed subscheme `X̃ ×_X P`. -/
theorem idealSheafData_pointBlowupExceptional :
    Scheme.CartierDivisor.idealSheafData (S.pointBlowupExceptional_isEffective P) =
      (Scheme.IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩).comap (S.pointBlowupProjection P) :=
  ((S.pointIdeal P).idealSheafData_exceptionalDivisor (S.isCoherent_pointIdeal P)).trans
    (congrArg (fun J => Scheme.IdealSheafData.comap J (S.pointBlowupProjection P))
      (S.quasicoherentIdealSubsheafEquiv_pointIdeal P))

/-- `E = π⁻¹(P)` set-theoretically: the support of `E` is the fibre of `π` over `P`. -/
theorem coe_support_pointBlowupExceptional :
    ((Scheme.CartierDivisor.idealSheafData (S.pointBlowupExceptional_isEffective P)).support :
      Set (S.pointBlowup P)) = S.pointBlowupProjection P ⁻¹' {P.1} := by
  rw [idealSheafData_pointBlowupExceptional, Scheme.IdealSheafData.support_comap,
    Closeds.coe_preimage, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-! ### The isomorphism off the center -/

/-- The open subscheme `X - P` of the surface. -/
def pointCompl : S.X.Opens :=
  ⟨{P.1}ᶜ, P.2.isOpen_compl⟩

/-- The open subscheme `X̃ - E` of the monoidal transformation: the complement of the support
of the exceptional divisor. -/
def pointBlowupExceptionalCompl : (S.pointBlowup P).Opens :=
  ⟨((Scheme.CartierDivisor.idealSheafData (S.pointBlowupExceptional_isEffective P)).support :
      Set (S.pointBlowup P))ᶜ,
    (Scheme.CartierDivisor.idealSheafData _).support.isClosed.isOpen_compl⟩

/-- `X̃ - E = π⁻¹(X - P)`. -/
theorem pointBlowupExceptionalCompl_eq :
    S.pointBlowupExceptionalCompl P = S.pointBlowupProjection P ⁻¹ᵁ S.pointCompl P := by
  ext1
  change (_ : Set (S.pointBlowup P))ᶜ = _
  rw [coe_support_pointBlowupExceptional]
  rfl

/-- `X - P` is the complement of the center of the blowing-up. -/
theorem pointCompl_eq_centerCompl : S.pointCompl P = (S.pointIdeal P).centerCompl := by
  ext1
  change {P.1}ᶜ = (Set.range _)ᶜ
  rw [range_subschemeι_pointIdeal]

/-- The projection `π` restricts to an isomorphism `π⁻¹(X - P) ⟶ X - P` (Proposition II.7.13(b)).
-/
theorem isIso_pointBlowupProjection_restrict :
    IsIso (S.pointBlowupProjection P ∣_ S.pointCompl P) := by
  rw [pointCompl_eq_centerCompl]
  exact (S.pointIdeal P).isIso_blowupProjection_restrict_centerCompl (S.isCoherent_pointIdeal P)

/-- **The monoidal transformation is an isomorphism off the center** (Hartshorne V.3, p. 386):
`π` restricts to an isomorphism `X̃ - E ≅ X - P`; it lies over `X`
(`pointBlowupIsoOffCenter_hom_ι`). -/
def pointBlowupIsoOffCenter :
    (S.pointBlowupExceptionalCompl P).toScheme ≅ (S.pointCompl P).toScheme :=
  have := S.isIso_pointBlowupProjection_restrict P
  (S.pointBlowup P).isoOfEq (S.pointBlowupExceptionalCompl_eq P) ≪≫
    asIso (S.pointBlowupProjection P ∣_ S.pointCompl P)

/-- The isomorphism `X̃ - E ≅ X - P` is the restriction of `π`. -/
@[reassoc]
theorem pointBlowupIsoOffCenter_hom_ι :
    (S.pointBlowupIsoOffCenter P).hom ≫ (S.pointCompl P).ι =
      (S.pointBlowupExceptionalCompl P).ι ≫ S.pointBlowupProjection P := by
  simp [pointBlowupIsoOffCenter, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

end Surface

end

end Hartshorne
