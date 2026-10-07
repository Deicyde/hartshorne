/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.LocalCotangentViaDifferentials
import Hartshorne.Scheme.TangentVectorsDualNumbers

/-!
# Tangent vectors via Kähler differentials

Hartshorne, *Algebraic Geometry*, II.8, Proposition 8.7 (p. 174).

For a local `k`-algebra with residue field `k`, this file identifies the dual of its cotangent
space with the dual of the fibre `Ω[B⁄k] ⊗[B] k` and with `k`-derivations.  At a rational point of
a `k`-scheme, it combines these equivalences with the dual-number classification.
-/

namespace Hartshorne

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

variable {k B : Type u} [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]

/-- A local `k`-algebra map from `B` to `k` identifies the residue field of `B` with `k`.

The target carries the `B`-algebra structure induced by the given map. -/
noncomputable def residueFieldAlgEquivOfLocalAlgHom
    (ρ : B →ₐ[k] k) [IsLocalHom ρ] :
    letI : Algebra B k := ρ.toRingHom.toAlgebra
    ResidueField B ≃ₐ[B] k := by
  letI : Algebra B k := ρ.toRingHom.toAlgebra
  let hρ : IsLocalHom ρ.toRingHom :=
    ⟨fun b hb ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _ ρ inferInstance b hb⟩
  let _ : IsLocalHom ρ.toRingHom := hρ
  let f : ResidueField B →ₐ[B] k :=
    { toRingHom := ResidueField.lift ρ.toRingHom
      commutes' := fun b ↦ ResidueField.lift_residue_apply ρ.toRingHom b }
  apply AlgEquiv.ofBijective f
  exact ⟨RingHom.injective f.toRingHom, fun z ↦
    ⟨algebraMap k (ResidueField B) z, by
      change ρ (algebraMap k B z) = z
      exact ρ.commutes z⟩⟩

/-- If a local `k`-algebra admits a local `k`-algebra residue map to `k`, then its canonical
coefficient-field map to the residue field is bijective. -/
theorem residueFieldAlgebraMap_bijective_of_localAlgHom
    (ρ : B →ₐ[k] k) [IsLocalHom ρ] :
    Function.Bijective (algebraMap k (ResidueField B)) := by
  constructor
  · exact RingHom.injective (algebraMap k (ResidueField B))
  · intro z
    obtain ⟨b, rfl⟩ := residue_surjective z
    refine ⟨ρ b, ?_⟩
    change residue B (algebraMap k B (ρ b)) = residue B b
    apply Ideal.Quotient.eq.mpr
    have hρsurj : Function.Surjective ρ := fun r ↦
      ⟨algebraMap k B r, by simp⟩
    have hker : RingHom.ker ρ.toRingHom = maximalIdeal B :=
      IsLocalRing.ker_eq_maximalIdeal ρ.toRingHom hρsurj
    rw [← hker, RingHom.mem_ker]
    simp

/-- Transport the differential fibre from the canonical residue field to the specified residue
field `k`. -/
noncomputable def differentialFiberResidueFieldEquiv
    (ρ : B →ₐ[k] k) [IsLocalHom ρ] :
    letI : Algebra B k := ρ.toRingHom.toAlgebra
    (Ω[B⁄k] ⊗[B] ResidueField B) ≃ₗ[k] (Ω[B⁄k] ⊗[B] k) := by
  letI : Algebra B k := ρ.toRingHom.toAlgebra
  exact (TensorProduct.congr (LinearEquiv.refl B Ω[B⁄k])
    (residueFieldAlgEquivOfLocalAlgHom ρ).toLinearEquiv).restrictScalars k

/-- The cotangent space of a local `k`-algebra with residue map `ρ` is the literal differential
fibre `Ω[B⁄k] ⊗[B] k`. -/
noncomputable def cotangentEquivDifferentialFiber
    (ρ : B →ₐ[k] k) [IsLocalHom ρ] :
    letI : Algebra B k := ρ.toRingHom.toAlgebra
    CotangentSpace B ≃ₗ[k] (Ω[B⁄k] ⊗[B] k) := by
  letI : Algebra B k := ρ.toRingHom.toAlgebra
  exact (localCotangentEquivDifferentials k B
    (residueFieldAlgebraMap_bijective_of_localAlgHom ρ)).trans
      (differentialFiberResidueFieldEquiv ρ)

/-- Dualizing the cotangent-to-differential-fibre equivalence identifies the two descriptions of
the Zariski tangent space. -/
noncomputable def cotangentDualEquivDifferentialFiberDual
    (ρ : B →ₐ[k] k) [IsLocalHom ρ] :
    letI : Algebra B k := ρ.toRingHom.toAlgebra
    (CotangentSpace B →ₗ[k] k) ≃ₗ[k] ((Ω[B⁄k] ⊗[B] k) →ₗ[k] k) := by
  letI : Algebra B k := ρ.toRingHom.toAlgebra
  exact LinearEquiv.congrLeft k k (cotangentEquivDifferentialFiber ρ)

/-- Linear functionals on the differential fibre are equivalent to `k`-derivations from `B` to
its specified residue field. -/
noncomputable def differentialFiberDualEquivDerivation
    (ρ : B →ₐ[k] k) [IsLocalHom ρ] :
    letI : Algebra B k := ρ.toRingHom.toAlgebra
    ((Ω[B⁄k] ⊗[B] k) →ₗ[k] k) ≃ ResidueDerivation ρ := by
  letI : Algebra B k := ρ.toRingHom.toAlgebra
  exact (cotangentDualEquivDifferentialFiberDual ρ).toEquiv.symm.trans
    (cotangentDualEquivDerivation ρ)

/-- Linear functionals on the differential fibre are equivalent to local lifts of the residue map
to the dual numbers. -/
noncomputable def differentialFiberDualEquivDualNumberLocalLift
    (ρ : B →ₐ[k] k) [IsLocalHom ρ] :
    letI : Algebra B k := ρ.toRingHom.toAlgebra
    ((Ω[B⁄k] ⊗[B] k) →ₗ[k] k) ≃ DualNumberLocalLift ρ := by
  letI : Algebra B k := ρ.toRingHom.toAlgebra
  exact (differentialFiberDualEquivDerivation ρ).trans
    (derivationEquivDualNumberLocalLift ρ)

private lemma rationalPointResidue_isLocalHom
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
    IsLocalHom (rationalPointResidueAlgHom X x) := by
  let _ : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  let hr : IsLocalHom (Scheme.stalkClosedPointTo (rationalPointHom x)).hom :=
    Scheme.isLocalHom_stalkClosedPointTo _
  exact ⟨fun a ha ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _
    (Scheme.stalkClosedPointTo (rationalPointHom x)).hom hr a ha⟩

/-- The fibre `Ω[𝒪_{X,x}⁄k] ⊗[𝒪_{X,x}] k` of Kähler differentials at a rational point. -/
noncomputable abbrev RationalPointDifferentialFiber
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) : Type u :=
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  let ρ := rationalPointResidueAlgHom X x
  letI : Algebra (RationalPointStalk X x) k := ρ.toRingHom.toAlgebra
  Ω[(RationalPointStalk X x)⁄k] ⊗[(RationalPointStalk X x)] k

/-- The differential-fibre description of the tangent space at a rational point. -/
noncomputable abbrev RationalPointDifferentialFiberDual
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) : Type u :=
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  let ρ := rationalPointResidueAlgHom X x
  letI : Algebra (RationalPointStalk X x) k := ρ.toRingHom.toAlgebra
  (Ω[(RationalPointStalk X x)⁄k] ⊗[(RationalPointStalk X x)] k) →ₗ[k] k

/-- The derivation description of the tangent space at a rational point. -/
noncomputable abbrev RationalPointDerivation
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) : Type u :=
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  ResidueDerivation (rationalPointResidueAlgHom X x)

/-- The Zariski tangent space at a rational point is the dual of the fibre of Kähler
differentials. -/
noncomputable def rationalPointTangentEquivDifferentialFiberDual
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    RationalPointTangentSpace X x ≃ RationalPointDifferentialFiberDual X x := by
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  let ρ := rationalPointResidueAlgHom X x
  let _ : IsLocalHom ρ := rationalPointResidue_isLocalHom X x
  letI : Algebra (RationalPointStalk X x) k := ρ.toRingHom.toAlgebra
  simpa only [RationalPointTangentSpace, RationalPointDifferentialFiberDual]
    using (cotangentDualEquivDifferentialFiberDual ρ).toEquiv

/-- The Zariski tangent space at a rational point is the space of `k`-derivations from its local
ring to its residue field. -/
noncomputable def rationalPointTangentEquivDerivation
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    RationalPointTangentSpace X x ≃ RationalPointDerivation X x := by
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  let ρ := rationalPointResidueAlgHom X x
  let _ : IsLocalHom ρ := rationalPointResidue_isLocalHom X x
  simpa only [RationalPointTangentSpace, RationalPointDerivation]
    using cotangentDualEquivDerivation ρ

/-- Differential-fibre functionals at a rational point are equivalent to derivations of its local
ring. -/
noncomputable def rationalPointDifferentialFiberDualEquivDerivation
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    RationalPointDifferentialFiberDual X x ≃ RationalPointDerivation X x :=
  (rationalPointTangentEquivDifferentialFiberDual X x).symm.trans
    (rationalPointTangentEquivDerivation X x)

/-- Pointed dual-number-valued points are equivalent to linear functionals on the fibre of
Kähler differentials. -/
noncomputable def dualNumberLiftEquivDifferentialFiberDual
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    DualNumberLift X x ≃ RationalPointDifferentialFiberDual X x :=
  (dualNumberLiftEquivTangentSpace X x).trans
    (rationalPointTangentEquivDifferentialFiberDual X x)

/-- The canonical map from pointed dual-number-valued points to differential-fibre tangent
functionals. -/
noncomputable def dualNumberLiftToDifferentialFiberDual
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    DualNumberLift X x → RationalPointDifferentialFiberDual X x :=
  dualNumberLiftEquivDifferentialFiberDual X x

/-- **Hartshorne II.8, Proposition 8.7.** Pointed maps from the dual numbers are in bijection with
linear functionals on the fibre `Ω[𝒪_{X,x}⁄k] ⊗[𝒪_{X,x}] k`. -/
theorem dualNumberLiftToDifferentialFiberDual_bijective
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    Function.Bijective (dualNumberLiftToDifferentialFiberDual X x) :=
  (dualNumberLiftEquivDifferentialFiberDual X x).bijective

end

end Hartshorne
