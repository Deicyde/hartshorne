/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Regular
import Hartshorne.Scheme.Differentials.DifferentialCriterionField
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular

/-!
# Infinitesimal lifting for a nonsingular affine scheme

Hartshorne, *Algebraic Geometry*, II, Exercise 8.6 (pp. 188–189).

Let `k` be an algebraically closed field and `A` a finitely generated `k`-algebra such that
`Spec A` is nonsingular (regular at every point). For every surjection of `k`-algebras
`B' → B` whose kernel has square zero and every `k`-algebra map `A → B`, there is a lift
`A → B'` (`Hartshorne.AffineNonsingularLifting.exists_lift_of_isRegular`).

## Proof

The lifting property for square-zero (indeed nilpotent) extensions is formal smoothness of `A`
over `k`; for a presentation `A = P/J` with `P` a polynomial ring it amounts to the splitting of
the conormal sequence `J/J² → Ω_{P/k} ⊗ A → Ω_{A/k} → 0`, as in Hartshorne's hint.

Formal smoothness of the finitely presented algebra `A` is checked on its smooth locus, which is
open, so it suffices to check it at the maximal ideals `𝔪` (every nonempty closed subset of
`Spec A` contains a closed point). There `A_𝔪` is regular with residue field `k`, so the fibre
`κ(𝔪) ⊗ Ω_{A/k}` is the cotangent space `𝔪/𝔪²` (Proposition 8.7), of dimension `dim A_𝔪`.
The differential criterion for smoothness over a field (whose proof is the local form of the
argument of Theorem 8.17: elements of `J` with independent differentials cut out `A_𝔪` in
`P_𝔪`, and the Jacobian criterion applies) then gives smoothness at `𝔪`
(`Hartshorne.AffineNonsingularLifting.isSmoothAt_of_isMaximal`).
-/

universe u v

open IsLocalRing Module TensorProduct AlgebraicGeometry

namespace Hartshorne

namespace AffineNonsingularLifting

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Let `A` be a finitely generated algebra over an algebraically closed field `k` and `𝔪` a
maximal ideal with `A_𝔪` regular. Then `A` is smooth over `k` at `𝔪`. -/
theorem isSmoothAt_of_isMaximal (m : Ideal A) [m.IsMaximal]
    [IsRegularLocalRing (Localization.AtPrime m)] :
    Algebra.IsSmoothAt k m := by
  have hbij := DifferentialsNonsingular.bijective_algebraMap_residueField (k := k) m
  have hcot := (IsRegularLocalRing.iff_finrank_cotangentSpace
    (R := Localization.AtPrime m)).mp inferInstance
  refine isSmoothAt_of_finrank_le m
    (finrank (ResidueField (Localization.AtPrime m)) (CotangentSpace (Localization.AtPrime m)))
    ?_ ?_
  · rw [DifferentialsNonsingular.finrank_tensor_kaehler_localization m.primeCompl
      (Localization.AtPrime m) m.ResidueField,
      ← finrank_cotangentSpace_eq_finrank_residueField_tensor_kaehlerDifferential k _ hbij]
  · rw [hcot, ringKrullDim_eq_zero_of_isField
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient m |>.mp ‹_›), add_zero]

/-- A finitely generated algebra `A` over an algebraically closed field `k` with `Spec A`
regular is formally smooth over `k`. -/
theorem formallySmooth_of_isRegular (hA : (Spec (CommRingCat.of A)).IsRegular) :
    Algebra.FormallySmooth k A := by
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  refine Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_of_forall fun q => ?_)
  by_contra hq
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  let x : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  have hx : x ∈ (Algebra.smoothLocus k A)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hq) Algebra.isOpen_smoothLocus.isClosed_compl
      ((PrimeSpectrum.le_iff_mem_closure q x).mp hqm)
  have : IsRegularLocalRing (Localization.AtPrime m) :=
    have : IsRegularLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk x) := hA.2 x
    IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (CommRingCat.of A) x).commRingCatIsoToRingEquiv
  exact hx (isSmoothAt_of_isMaximal (k := k) m)

/-- **Hartshorne II, Exercise 8.6** (the infinitesimal lifting property). Let `k` be an
algebraically closed field and `A` a finitely generated `k`-algebra such that `Spec A` is
nonsingular. Let `g : B' → B` be a surjection of `k`-algebras whose kernel `I` satisfies
`I² = 0`, and let `f : A → B` be a `k`-algebra homomorphism. Then there is a `k`-algebra
homomorphism `f' : A → B'` with `g ∘ f' = f`.

Hartshorne asks for `Spec A` to be a nonsingular variety; here `Spec A` is only assumed regular
at every point, not irreducible. -/
theorem exists_lift_of_isRegular (hA : (Spec (CommRingCat.of A)).IsRegular)
    {B' B : Type v} [CommRing B'] [CommRing B] [Algebra k B'] [Algebra k B]
    (g : B' →ₐ[k] B) (hg : Function.Surjective g) (hI : RingHom.ker g ^ 2 = ⊥)
    (f : A →ₐ[k] B) :
    ∃ f' : A →ₐ[k] B', g.comp f' = f := by
  have := formallySmooth_of_isRegular (k := k) hA
  have hnil : IsNilpotent (RingHom.ker (g : B' →+* B)) :=
    ⟨2, by rw [RingHom.ker_coe_toRingHom, hI, Ideal.zero_eq_bot]⟩
  exact ⟨Algebra.FormallySmooth.liftOfSurjective f g hg hnil,
    Algebra.FormallySmooth.comp_liftOfSurjective f g hg hnil⟩

end AffineNonsingularLifting

end Hartshorne
