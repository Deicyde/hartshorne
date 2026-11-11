/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.InvertibleSectionDivisor
import Hartshorne.Scheme.RegularLocalFactorial
import Hartshorne.Scheme.Regular
import Hartshorne.Scheme.CartierClassPicardIntegral
import Hartshorne.Scheme.ProjectiveSpaceProper

/-!
# Divisors of zeros on a nonsingular projective variety

Hartshorne, *Algebraic Geometry*, II.7, Proposition 7.7 (pp. 156–157), in the book's setting:
`X` is a nonsingular projective variety over an algebraically closed field `k`. Here this means an
integral scheme `X` with a projective morphism `p : X ⟶ Spec k` (`Hartshorne.Projective`) all of
whose local rings are regular (`Scheme.IsRegular`).

The statements are corollaries of the general forms in
`Hartshorne.Scheme.InvertibleSectionDivisor`:

* `X` is Noetherian and separated, being projective over a field
  (`Scheme.isNoetherian_of_projective`, `Scheme.isSeparated_of_projective`);
* `X` is locally factorial (Remark 6.11.1A, `Scheme.isLocallyFactorial_of_isRegularLocalRing`), so
  Weil and Cartier divisors agree (Proposition 6.11) and every Weil divisor `D₀` has an invertible
  sheaf `𝒪_X(D₀)`;
* every invertible sheaf is some `𝒪_X(D₀)` (Proposition 6.15 and Corollary 6.16,
  `Scheme.exists_cartierDivisor_sheaf_iso`);
* a projective morphism is proper, hence universally closed, so `Γ(X, 𝒪_X) = k` when `k` is
  algebraically closed, which gives (c).

Parts (a) and (b) do not use that `k` is algebraically closed, so they are stated over any field.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

namespace Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A scheme projective over a field is Noetherian. -/
theorem isNoetherian_of_projective (p : X ⟶ Spec (.of k)) (hp : Hartshorne.Projective p) :
    IsNoetherian X := by
  have := hp.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact {}

/-- A scheme projective over a field is separated. -/
theorem isSeparated_of_projective (p : X ⟶ Spec (.of k)) (hp : Hartshorne.Projective p) :
    X.IsSeparated := by
  have := hp.isProper
  refine ⟨?_⟩
  rw [show terminal.from X = p ≫ terminal.from _ from terminal.hom_ext _ _]
  infer_instance

/-- A regular scheme is locally factorial (Hartshorne II, Remark 6.11.1A). -/
theorem IsRegular.isLocallyFactorial (hreg : X.IsRegular) : X.IsLocallyFactorial :=
  X.isLocallyFactorial_of_isRegularLocalRing hreg.2

variable [IsIntegral X]

/-- **Hartshorne II, Proposition 7.7(a)**, on a nonsingular projective variety. Let `X` be an
integral regular scheme projective over a field `k`, `D₀` a Weil divisor on `X` and
`L ≅ 𝒪_X(D₀)`. Every nonzero global section `s` of `L` has a divisor of zeros `(s)₀`, which is
effective and linearly equivalent to `D₀`. Hartshorne takes `k` algebraically closed; the
argument does not use it. -/
theorem exists_isDivisorOfZeros_of_projective (p : X ⟶ Spec (.of k))
    (hp : Hartshorne.Projective p) (hreg : X.IsRegular) :
    letI := isNoetherian_of_projective p hp
    letI := isSeparated_of_projective p hp
    ∀ {D₀ : X.WeilDivisor} {L : X.Modules},
      (L ≅ (weilCartierEquiv hreg.isLocallyFactorial D₀).sheaf) →
      ∀ {s : L.val.obj (op ⊤)}, s ≠ 0 → ∃ D : X.WeilDivisor,
        CartierDivisor.IsDivisorOfZeros L s (weilCartierEquiv hreg.isLocallyFactorial D) ∧
          WeilDivisor.IsEffective D ∧
          WeilDivisor.LinearEquivalent
            (satisfiesConditionStar_of_isLocallyFactorial hreg.isLocallyFactorial) D D₀ := by
  let := isNoetherian_of_projective p hp
  let := isSeparated_of_projective p hp
  intro D₀ L φ s hs
  exact (weil_isDivisorOfZeros hreg.isLocallyFactorial φ).1 s hs

/-- **Hartshorne II, Proposition 7.7(a)** for an invertible sheaf, on a nonsingular projective
variety. Let `X` be an integral regular scheme projective over a field `k` and `L` an invertible
sheaf. Then `L ≅ 𝒪_X(D₀)` for a Weil divisor `D₀` (Proposition 6.11 and Corollary 6.16), and
every nonzero global section `s` of `L` has a divisor of zeros `(s)₀`, which is effective and
linearly equivalent to `D₀`. Hartshorne takes `k` algebraically closed; the argument does not use
it. -/
theorem exists_isDivisorOfZeros_of_isInvertible_of_projective (p : X ⟶ Spec (.of k))
    (hp : Hartshorne.Projective p) (hreg : X.IsRegular) {L : X.Modules} (hL : L.IsInvertible) :
    letI := isNoetherian_of_projective p hp
    letI := isSeparated_of_projective p hp
    ∃ D₀ : X.WeilDivisor, Nonempty (L ≅ (weilCartierEquiv hreg.isLocallyFactorial D₀).sheaf) ∧
      ∀ s : L.val.obj (op ⊤), s ≠ 0 → ∃ D : X.WeilDivisor,
        CartierDivisor.IsDivisorOfZeros L s (weilCartierEquiv hreg.isLocallyFactorial D) ∧
          WeilDivisor.IsEffective D ∧
          WeilDivisor.LinearEquivalent
            (satisfiesConditionStar_of_isLocallyFactorial hreg.isLocallyFactorial) D D₀ := by
  let := isNoetherian_of_projective p hp
  let := isSeparated_of_projective p hp
  obtain ⟨E, ⟨χ⟩⟩ := exists_cartierDivisor_sheaf_iso hL
  have hE : (weilCartierEquiv hreg.isLocallyFactorial
      ((weilCartierEquiv hreg.isLocallyFactorial).symm E)).sheaf = E.sheaf := by
    rw [AddEquiv.apply_symm_apply]
  exact ⟨_, ⟨χ.symm ≪≫ eqToIso hE.symm⟩,
    fun s hs ↦ exists_isDivisorOfZeros_of_projective p hp hreg (χ.symm ≪≫ eqToIso hE.symm) hs⟩

/-- **Hartshorne II, Proposition 7.7(b)**, on a nonsingular projective variety. Let `X` be an
integral regular scheme projective over a field `k`, `D₀` a Weil divisor on `X` and
`L ≅ 𝒪_X(D₀)`. Every effective Weil divisor linearly equivalent to `D₀` is the divisor of zeros of
a nonzero global section of `L`. Hartshorne takes `k` algebraically closed; the argument does not
use it. -/
theorem exists_section_isDivisorOfZeros_of_projective (p : X ⟶ Spec (.of k))
    (hp : Hartshorne.Projective p) (hreg : X.IsRegular) :
    letI := isNoetherian_of_projective p hp
    letI := isSeparated_of_projective p hp
    ∀ {D₀ : X.WeilDivisor} {L : X.Modules},
      (L ≅ (weilCartierEquiv hreg.isLocallyFactorial D₀).sheaf) → ∀ {D : X.WeilDivisor},
      WeilDivisor.IsEffective D →
      WeilDivisor.LinearEquivalent
        (satisfiesConditionStar_of_isLocallyFactorial hreg.isLocallyFactorial) D D₀ →
        ∃ s : L.val.obj (op ⊤), s ≠ 0 ∧
          CartierDivisor.IsDivisorOfZeros L s (weilCartierEquiv hreg.isLocallyFactorial D) := by
  let := isNoetherian_of_projective p hp
  let := isSeparated_of_projective p hp
  intro D₀ L φ D hD hlin
  exact (weil_isDivisorOfZeros hreg.isLocallyFactorial φ).2 D hD hlin

/-- **Hartshorne II, Proposition 7.7(c)**, on a nonsingular projective variety. Let `X` be an
integral regular scheme projective over an algebraically closed field `k`, `D₀` a Weil divisor on
`X` and `L ≅ 𝒪_X(D₀)`. Two nonzero global sections `s, s'` of `L` have the same divisor of zeros
if and only if `s' = λ s` for some `λ ∈ kˣ`. -/
theorem isDivisorOfZeros_eq_iff_of_projective [IsAlgClosed k] (p : X ⟶ Spec (.of k))
    (hp : Hartshorne.Projective p) (hreg : X.IsRegular) :
    letI := isNoetherian_of_projective p hp
    letI := isSeparated_of_projective p hp
    ∀ {D₀ : X.WeilDivisor} {L : X.Modules},
      (L ≅ (weilCartierEquiv hreg.isLocallyFactorial D₀).sheaf) →
      ∀ {s s' : L.val.obj (op ⊤)}, s ≠ 0 → s' ≠ 0 → ∀ {D D' : X.WeilDivisor},
      CartierDivisor.IsDivisorOfZeros L s (weilCartierEquiv hreg.isLocallyFactorial D) →
      CartierDivisor.IsDivisorOfZeros L s' (weilCartierEquiv hreg.isLocallyFactorial D') →
        (D = D' ↔
          ∃ c : kˣ, s' = (show X.ringCatSheaf.obj.obj (op ⊤) from globalScalar p c) • s) := by
  let := isNoetherian_of_projective p hp
  let := isSeparated_of_projective p hp
  have := hp.isProper
  intro D₀ L φ s s' hs hs' D D' hD hD'
  exact weil_isDivisorOfZeros_eq_iff p hreg.isLocallyFactorial φ hs hs' hD hD'

end Scheme

end AlgebraicGeometry
