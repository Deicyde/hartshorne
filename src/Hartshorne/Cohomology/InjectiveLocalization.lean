/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Localization of injective modules

The canonical map from an injective module over a Noetherian ring to its
localization at one element is surjective.
-/

universe u

namespace Hartshorne

/-- If `I` is injective over a Noetherian commutative ring `A`, every element
of the localization of `I` at the powers of `f` comes from `I`. -/
theorem injectiveLocalizationMap_surjective
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Type u) [AddCommGroup I] [Module A I]
    [Module.Injective A I] (f : A) :
    Function.Surjective
      (LocalizedModule.mkLinearMap (Submonoid.powers f) I) := by
  classical
  let mu : Module.End A A := Module.toModuleEnd A A f
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 (LinearMap.eventually_iSup_ker_pow_eq mu)
  have hker : (⨆ m, LinearMap.ker (mu ^ m)) = LinearMap.ker (mu ^ N) :=
    hN N le_rfl
  have hmu_apply (m : ℕ) (a : A) : (mu ^ m) a = f ^ m * a := by
    rw [← map_pow]
    rfl
  intro y
  induction y using LocalizedModule.induction_on with
  | _ x s =>
      obtain ⟨n, hn⟩ :=
        (Submonoid.mem_powers_iff (s : A) f).mp s.property
      let mum : Module.End A A := mu ^ (n + N)
      let psi : A →ₗ[A] I := LinearMap.toSpanSingleton A I (f ^ N • x)
      have hkerpsi : LinearMap.ker mum ≤ LinearMap.ker psi := by
        intro a ha
        have haSup : a ∈ ⨆ m, LinearMap.ker (mu ^ m) := by
          exact (le_iSup (fun m => LinearMap.ker (mu ^ m)) (n + N)) ha
        have haN : a ∈ LinearMap.ker (mu ^ N) := by
          rw [← hker]
          exact haSup
        have haN' : f ^ N * a = 0 := by
          simpa [LinearMap.mem_ker, hmu_apply] using haN
        change a • (f ^ N • x) = 0
        rw [← mul_smul, mul_comm, haN', zero_smul]
      let phi : LinearMap.range mum →ₗ[A] I :=
        ((LinearMap.ker mum).liftQ psi hkerpsi).comp
          mum.quotKerEquivRange.symm.toLinearMap
      have hBaer : Module.Baer A I :=
        Module.Baer.of_injective (inferInstance : Module.Injective A I)
      obtain ⟨Phi, hPhi⟩ := hBaer (LinearMap.range mum) phi
      let r : LinearMap.range mum := ⟨mum 1, by exact ⟨1, rfl⟩⟩
      have hphi : phi r = f ^ N • x := by
        change ((LinearMap.ker mum).liftQ psi hkerpsi)
          (mum.quotKerEquivRange.symm r) = f ^ N • x
        rw [show mum.quotKerEquivRange.symm r =
            (LinearMap.ker mum).mkQ 1 from
          LinearMap.quotKerEquivRange_symm_apply_image mum 1 r.property]
        simp [psi]
      have hz : f ^ (n + N) • Phi 1 = f ^ N • x := by
        calc
          f ^ (n + N) • Phi 1 = mum 1 • Phi 1 := by
            rw [hmu_apply]
            simp
          _ = Phi (mum 1) := by
            simpa using (Phi.map_smul (mum 1) (1 : A)).symm
          _ = phi r := hPhi (mum 1) r.property
          _ = f ^ N • x := hphi
      refine ⟨Phi 1, ?_⟩
      rw [LocalizedModule.mkLinearMap_apply]
      apply (LocalizedModule.mk_eq).2
      let t : Submonoid.powers f :=
        ⟨f ^ N, (Submonoid.mem_powers_iff (f ^ N) f).2 ⟨N, rfl⟩⟩
      refine ⟨t, ?_⟩
      simp only [Submonoid.smul_def, t, one_smul]
      rw [← hn]
      rw [smul_smul, ← pow_add]
      simpa [add_comm] using hz

end Hartshorne
