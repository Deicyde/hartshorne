/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.LinearSeparation
import Hartshorne.Projective.LocalFraction

/-!
# A local ring determines its point

Hartshorne, *Algebraic Geometry*, I.6, Lemma 6.4 (p. 41).
-/

namespace Hartshorne

open MvPolynomial

universe u v

variable {k : Type u} [Field k] {σ : Type v}
  {Y : Set (ProjectiveSpace k σ)}

/-- **Hartshorne I.6, Lemma 6.4.** On a quasi-projective variety, inclusion of
local rings inside the function field determines the point. -/
theorem IsQuasiProjVariety.eq_of_localRingRange_le
    (hY : IsQuasiProjVariety Y)
    {P Q : (Variety.ofQuasiProjective hY).carrier}
    (hle : (Variety.ofQuasiProjective hY).localRingRange Q ≤
      (Variety.ofQuasiProjective hY).localRingRange P) :
    P = Q := by
  by_contra hPQ
  have hPQ' : P.1 ≠ Q.1 := by
    intro h
    exact hPQ (Subtype.ext h)
  obtain ⟨g, h, hg, hh, hgP, hgQ, hhP, hhQ⟩ :=
    exists_linear_forms_separating_projective_points hPQ'
  have hne : ∃ R ∈ Y, eval R.rep h ≠ 0 := by
    exact ⟨Q.1, Q.2, by simpa [HomogeneousVanish] using hhQ⟩
  let q := projRatClass hY hg hh hne
  have hqQ : q ∈ (Variety.ofQuasiProjective hY).localRingRange Q :=
    (projRatClass_mem_localRingRange_iff hY Q hg hh hne hgQ).2 hhQ
  have hqP : q ∈ (Variety.ofQuasiProjective hY).localRingRange P :=
    hle hqQ
  have hhP' : ¬ HomogeneousVanish h P.1 :=
    (projRatClass_mem_localRingRange_iff hY P hg hh hne hgP).1 hqP
  exact hhP' hhP

end Hartshorne
