/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.CanonicalSectionRing
import Hartshorne.Scheme.TensorPowerSectionRingMap
import Hartshorne.Scheme.CartierDivisorSheafArithmetic
import Hartshorne.RingedSpace.ModuleGluing

/-!
# The canonical section ring through a canonical divisor

Hartshorne writes the canonical ring as `R(X, K) = ⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))` for a canonical
divisor `K`, while `Hartshorne.CanonicalSectionRing` is defined through `ω_X^{⊗ n}`. A chosen
isomorphism `φ : 𝒪_X(K) ≅ ω_X` induces isomorphisms `𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n} ≅ ω_X^{⊗ n}`
(`AlgebraicGeometry.Scheme.CartierDivisor.nsmulSheafIso`, `Hartshorne.canonicalDivisorPowIso`),
and a graded ring isomorphism `⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n}) ≃+* R(X, K)`
(`Hartshorne.canonicalSectionRingEquivOfIso`).
-/

open CategoryTheory Opposite TopologicalSpace
open scoped DirectSum

namespace AlgebraicGeometry

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Scheme.CartierDivisor

open Hartshorne Hartshorne.Ringed

variable {X : Scheme.{u}}

theorem zero_restrict_top : (0 : X.CartierDivisor).restrict ⊤ =
    X.toCartierDivisorSheaf.hom.app (op ⊤)
      (Additive.ofMul (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))) := by
  rw [show (0 : X.CartierDivisor).restrict ⊤ = 0 from map_zero _]
  exact (map_zero _).symm

/-- The morphism `𝒪_X ⟶ 𝒪_X(0)`, `r ↦ r`. -/
def fromStructureZero : structureModule X.sheaf ⟶ (0 : X.CartierDivisor).sheafR :=
  modulesHomMk (fun U => (0 : X.CartierDivisor).generatorMap zero_restrict_top le_top)
    (fun U V i x => by
      apply Subtype.ext
      change X.toK V (X.presheaf.map (homOfLE i).op x) *
          X.totalQuotientSheaf.obj.map (homOfLE le_top).op
            (kUnitVal (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))⁻¹) =
        X.totalQuotientSheaf.obj.map (homOfLE i).op (X.toK U x *
          X.totalQuotientSheaf.obj.map (homOfLE le_top).op
            (kUnitVal (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))⁻¹))
      have h1 : kUnitVal (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))⁻¹ = 1 := by
        rw [inv_one]
        exact Units.val_one
      rw [h1, map_one, mul_one]
      refine (toK_naturality i x).symm.trans (congrArg _ ?_)
      rw [map_one, mul_one])

theorem isIso_fromStructureZero : IsIso (fromStructureZero (X := X)) :=
  ModuleGluing.isIso_of_bijective _ fun U =>
    (0 : X.CartierDivisor).generatorMap_bijective zero_restrict_top (le_top : U.unop ≤ ⊤)

/-- **`𝒪_X(0) ≅ 𝒪_X`.** -/
def zeroSheafIso : (0 : X.CartierDivisor).sheafR ≅ structureModule X.sheaf :=
  haveI := isIso_fromStructureZero (X := X)
  (asIso fromStructureZero).symm

/-- **`𝒪_X(nD) ≅ 𝒪_X(D)^{⊗ n}`**, by induction on `n` from `𝒪_X(0) ≅ 𝒪_X` and
`𝒪_X(nD) ⊗ 𝒪_X(D) ≅ 𝒪_X(nD + D)`. -/
def nsmulSheafIso (D : X.CartierDivisor) :
    ∀ n : ℕ, (n • D).sheafR ≅ moduleSheafTensorPower n D.sheafR
  | 0 => eqToIso (congrArg sheafR (zero_nsmul D)) ≪≫ zeroSheafIso ≪≫
      (moduleSheafTensorPowerZeroIso D.sheafR).symm
  | n + 1 => eqToIso (congrArg sheafR (succ_nsmul D n)) ≪≫ (tensorIso (n • D) D).symm ≪≫
      moduleSheafTensorIsoOfIso (nsmulSheafIso D n) (Iso.refl _) ≪≫
      (moduleSheafTensorPowerSuccIso D.sheafR n).symm

end Scheme.CartierDivisor

end

end AlgebraicGeometry

namespace Hartshorne

open AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The isomorphisms `𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n} ≅ ω_X^{⊗ n}` induced by `φ : 𝒪_X(K) ≅ ω_X`. -/
noncomputable def canonicalDivisorPowIso {K : X.CartierDivisor} (φ : K.sheaf ≅ canonicalSheaf f)
    (n : ℕ) : (n • K).sheafR ≅ moduleSheafTensorPower (R := X.sheaf) n (canonicalSheaf f) :=
  K.nsmulSheafIso n ≪≫ TensorPowerSectionRing.powIso φ n

/-- The degree-`n` part `H⁰(X, 𝒪_X(K)^{⊗ n})` of the section ring of `𝒪_X(K)`. -/
abbrev divisorSectionRingComponent (K : X.CartierDivisor) (n : ℕ) : Type u :=
  TensorPowerSectionRing.Component (R := X.sheaf) K.sheaf (op ⊤) n

/-- The graded ring structure on `n ↦ H⁰(X, 𝒪_X(K)^{⊗ n})`. -/
noncomputable instance divisorSectionRingComponent.gRing (K : X.CartierDivisor) :
    DirectSum.GRing (divisorSectionRingComponent K) :=
  TensorPowerSectionRing.gRing (R := X.sheaf) K.sheaf (op ⊤)

/-- **The canonical section ring through a canonical divisor.** An isomorphism
`φ : 𝒪_X(K) ≅ ω_X` induces a graded ring isomorphism `⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n}) ≃+* R(X, K)`,
which in degree `n` is `H⁰(X, φ^{⊗ n})` (`canonicalSectionRingEquivOfIso_of`). -/
noncomputable def canonicalSectionRingEquivOfIso {K : X.CartierDivisor}
    (φ : K.sheaf ≅ canonicalSheaf f) :
    (⨁ n, divisorSectionRingComponent K n) ≃+* CanonicalSectionRing f :=
  TensorPowerSectionRing.ringEquiv φ (op ⊤)

theorem canonicalSectionRingEquivOfIso_of {K : X.CartierDivisor} (φ : K.sheaf ≅ canonicalSheaf f)
    (n : ℕ) (a : divisorSectionRingComponent K n) :
    canonicalSectionRingEquivOfIso f φ (DirectSum.of _ n a) =
      DirectSum.of _ n ((TensorPowerSectionRing.powIso φ n).hom.val.app (op ⊤) a) :=
  TensorPowerSectionRing.ringEquiv_of φ (op ⊤) n a

/-- The sections over `U` of an isomorphism of sheaves of modules, as an additive equivalence. -/
noncomputable def sectionsAddEquiv {A B : SheafOfModules.{u} (ringCatSheafOf X.sheaf)} (e : A ≅ B)
    (U : X.Opensᵒᵖ) : A.val.obj U ≃+ B.val.obj U where
  toFun := e.hom.val.app U
  invFun := e.inv.val.app U
  left_inv x := by
    change (e.hom ≫ e.inv).val.app U x = x
    rw [e.hom_inv_id]
    rfl
  right_inv x := by
    change (e.inv ≫ e.hom).val.app U x = x
    rw [e.inv_hom_id]
    rfl
  map_add' := map_add _

/-- Hartshorne's presentation `⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))` of the section ring of a divisor `K`.
Its ring structure (`DivisorMultipleSectionRing.instRing`) is transported from
`⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n})` along the isomorphisms `𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n}`
(`AlgebraicGeometry.Scheme.CartierDivisor.nsmulSheafIso`). -/
def DivisorMultipleSectionRing (K : X.CartierDivisor) : Type u :=
  ⨁ n : ℕ, (n • K).sheafR.val.obj (op ⊤)

/-- The additive equivalence `⨁ₙ H⁰(X, 𝒪_X(nK)) ≃+ ⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n})`, degreewise
`H⁰(X, 𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n})`. -/
noncomputable def divisorMultipleSectionsAddEquiv (K : X.CartierDivisor) :
    (⨁ n : ℕ, (n • K).sheafR.val.obj (op ⊤)) ≃+ ⨁ n, divisorSectionRingComponent K n :=
  DFinsupp.mapRange.addEquiv fun n => sectionsAddEquiv (K.nsmulSheafIso n) (op ⊤)

noncomputable instance DivisorMultipleSectionRing.instRing (K : X.CartierDivisor) :
    Ring (DivisorMultipleSectionRing K) :=
  (divisorMultipleSectionsAddEquiv K).toEquiv.ring

/-- The ring isomorphism `⨁ₙ H⁰(X, 𝒪_X(nK)) ≃+* ⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n})`. -/
noncomputable def divisorMultipleSectionRingEquiv (K : X.CartierDivisor) :
    DivisorMultipleSectionRing K ≃+* ⨁ n, divisorSectionRingComponent K n :=
  (divisorMultipleSectionsAddEquiv K).toEquiv.ringEquiv

/-- **A canonical divisor presents the canonical section ring.** For a Cartier divisor `K` and an
isomorphism `φ : 𝒪_X(K) ≅ ω_X` (for instance from `Hartshorne.exists_cartierDivisor_canonicalDivisorClass`),
there is a graded ring isomorphism `⨁ₙ H⁰(X, 𝒪_X(nK)) ≃+* R(X, K) = ⨁ₙ H⁰(X, ω_X^{⊗ n})`, which in
degree `n` is `H⁰` of the isomorphism `𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n} ≅ ω_X^{⊗ n}` induced by `φ`
(`canonicalSectionRingEquivOfDivisor_of`). -/
noncomputable def canonicalSectionRingEquivOfDivisor {K : X.CartierDivisor}
    (φ : K.sheaf ≅ canonicalSheaf f) : DivisorMultipleSectionRing K ≃+* CanonicalSectionRing f :=
  (divisorMultipleSectionRingEquiv K).trans (canonicalSectionRingEquivOfIso f φ)

theorem canonicalSectionRingEquivOfDivisor_of {K : X.CartierDivisor}
    (φ : K.sheaf ≅ canonicalSheaf f) (n : ℕ) (s : (n • K).sheafR.val.obj (op ⊤)) :
    canonicalSectionRingEquivOfDivisor f φ
        (DirectSum.of (fun n : ℕ => (n • K).sheafR.val.obj (op ⊤)) n s) =
      DirectSum.of _ n ((canonicalDivisorPowIso f φ n).hom.val.app (op ⊤) s) := by
  change canonicalSectionRingEquivOfIso f φ (divisorMultipleSectionsAddEquiv K
    (DirectSum.of _ n s)) = _
  rw [show divisorMultipleSectionsAddEquiv K (DirectSum.of _ n s) =
      DirectSum.of _ n ((K.nsmulSheafIso n).hom.val.app (op ⊤) s) from
    DFinsupp.mapRange_single (hf := fun _ => map_zero _), canonicalSectionRingEquivOfIso_of]
  rfl

end Hartshorne
