/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.AffineGermCompare
import Hartshorne.Morphism.LocalRingLocalization
import Hartshorne.Morphism.VarietyLocalRingHom
import Hartshorne.Rational.AffineOpenBasis
import Mathlib.RingTheory.Localization.Submodule

/-!
# Local rings on open neighbourhoods

Toward Hartshorne, *Algebraic Geometry*, I.5, Theorem 5.3 (p. 33).

Passing from a variety to an open neighbourhood of a point does not change its
local ring.  Consequently, a variety admitting an affine-open basis has a
Noetherian local ring at every point: shrink to an affine neighbourhood and
use the description of its local ring as a localization of its coordinate
ring.
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k]

namespace Variety

variable {X : Variety.{u, v} k} {U : Opens X.carrier}
  {hU : (U : Set X.carrier).Nonempty}

/-- A germ on an open subvariety, viewed as a germ on the ambient variety. -/
private noncomputable def GermRep.pushToAmbient
    {P : (X.restrict U hU).carrier} (r : GermRep (X.restrict U hU) P) :
    GermRep X P.1 where
  U := pushOpens U r.U
  mem_U := ⟨P.2, fun _ => r.mem_U⟩
  toFun := fun x => r.toFun (ofPush x)
  regular := r.regular

/-- Pullback along the inclusion of an open subvariety is a bijection on local
rings.  This is the canonical isomorphism
`𝒪_{P,X} ≃+* 𝒪_{P,X|U}`. -/
theorem bijective_localRingHom_inclHom
    (P : (X.restrict U hU).carrier) :
    Function.Bijective ((X.inclHom U hU).localRingHom P) := by
  constructor
  · refine Quotient.ind fun r => Quotient.ind fun s => fun hrs => ?_
    have hrel := Quotient.exact hrs
    refine Quotient.sound ?_
    set W : Opens X.carrier := r.U ⊓ s.U with hW
    have hfr : (fun x : W => r.toFun ⟨x.1, x.2.1⟩) ∈ X.regular W :=
      X.regular_restrict inf_le_left r.regular
    have hfs : (fun x : W => s.toFun ⟨x.1, x.2.2⟩) ∈ X.regular W :=
      X.regular_restrict inf_le_right s.regular
    have hVopen : IsOpen {x : W | x.1 ∈ U} :=
      U.isOpen.preimage continuous_subtype_val
    have hPW : (⟨P.1, r.mem_U, s.mem_U⟩ : W) ∈ {x : W | x.1 ∈ U} := P.2
    have heq := Variety.eq_of_eqOn hfr hfs hVopen ⟨_, hPW⟩ fun x hx =>
      hrel ⟨x.1, hx⟩ x.2.1 x.2.2
    exact fun x hr hs => congrFun heq ⟨x, hr, hs⟩
  · refine Quotient.ind fun r => ?_
    refine ⟨Quotient.mk _ r.pushToAmbient, ?_⟩
    exact Quotient.sound fun _ _ _ => rfl

/-- The ring equivalence induced by inclusion of an open neighbourhood. -/
noncomputable def localRingEquivRestrict
    (P : (X.restrict U hU).carrier) :
    LocalRingAt (X.restrict U hU) P ≃+* LocalRingAt X P.1 :=
  (RingEquiv.ofBijective ((X.inclHom U hU).localRingHom P)
    (bijective_localRingHom_inclHom P)).symm

/-- If affine opens form a basis on `X`, then every local ring of `X` is
Noetherian. -/
theorem HasAffineOpenBasis.isNoetherianRing_localRingAt
    {X : Variety k} (hX : X.HasAffineOpenBasis) (P : X.carrier) :
    IsNoetherianRing (LocalRingAt X P) := by
  obtain ⟨V, hV, hPV, -, τ, hτ, Z, hZ, φ, hφ⟩ := hX ⊤ P trivial
  let _ : Finite τ := hτ
  let Q : (X.restrict V hV).carrier := ⟨P, hPV⟩
  let eOpen : LocalRingAt (X.restrict V hV) Q ≃+* LocalRingAt X P :=
    localRingEquivRestrict Q
  let eIso : LocalRingAt (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) (φ Q)
      ≃+* LocalRingAt (X.restrict V hV) Q :=
    RingEquiv.ofBijective (φ.localRingHom Q)
      (VarietyHom.bijective_localRingHom_of_isIso hφ Q)
  let eAffine := localRingEquivAffine hZ.isQuasiAffineVariety (φ Q)
  let eLocalization := localizationEquivLocalRing hZ.isIrreducible
    (affinePoint hZ.isQuasiAffineVariety (φ Q))
  let _ : IsNoetherianRing (coordinateRing Z) :=
    Algebra.FiniteType.isNoetherianRing k (coordinateRing Z)
  let _ : IsNoetherianRing
      (Localization.AtPrime (maximalIdealAt Z
        (affinePoint hZ.isQuasiAffineVariety (φ Q)))) := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (((eLocalization.trans eAffine.symm).trans eIso).trans eOpen)

end Variety

end Hartshorne
