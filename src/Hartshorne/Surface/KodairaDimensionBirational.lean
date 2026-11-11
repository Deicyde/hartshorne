/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.KodairaDimension
import Hartshorne.Surface.CanonicalRingBirational

/-!
# The Kodaira dimension is a birational invariant

Hartshorne, *Algebraic Geometry*, V.6 (p. 421): the Kodaira dimension
`κ(X) = trdeg_k R(X, K) - 1` is a birational invariant.

Birationally equivalent nonsingular varieties, proper over an algebraically closed field `k`,
have isomorphic canonical section rings as graded rings, through `k`-linear isomorphisms in each
degree (`Hartshorne.canonicalSectionRing_ringEquiv_of_birational`). Such a ring isomorphism
fixes the unit section in degree `0`, hence, by `k`-linearity in degree `0`, commutes with the
structure maps `k → R(X, K)`; it is therefore a `k`-algebra isomorphism and preserves the
transcendence degree over `k` (`Hartshorne.kodairaDimension_eq_of_birational`). The `-1` case
is included, since the integer `κ(X)` is read off from the transcendence degree in all cases.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace Hartshorne

universe u

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] [IsAlgClosed k] {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
  (pX : X ⟶ Spec (.of k)) (pX' : X' ⟶ Spec (.of k)) [IsProper pX] [IsProper pX']

/-- **The Kodaira dimension is a birational invariant** (Hartshorne V.6, p. 421). Let `X` and
`X'` be nonsingular varieties, proper over an algebraically closed field `k`, and birationally
equivalent over `k` (a partial isomorphism `X ⤏ X'` over `k`). Then `κ(X) = κ(X')`, including
the case `κ = -1`. Here `X`, `X'` are integral regular schemes proper over `k`, not necessarily
projective; the invertibility of the canonical sheaves, needed to define `κ`, holds automatically
for such schemes (`Hartshorne.canonicalSheaf_isInvertible`). -/
theorem kodairaDimension_eq_of_birational (hX : X.IsRegular) (hX' : X'.IsRegular)
    (hω : (canonicalSheaf pX).IsInvertible) (hω' : (canonicalSheaf pX').IsInvertible)
    (hbir : ∃ e : X.PartialIso X', e.IsOver pX pX') :
    kodairaDimension pX hω = kodairaDimension pX' hω' := by
  obtain ⟨E, ψ, hE⟩ := canonicalSectionRing_ringEquiv_of_birational pX pX' hX hX' hbir
  let _ := TensorPowerSectionRing.commRing (R := X.sheaf) (canonicalSheaf pX) (op ⊤)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 hω)
  let _ := TensorPowerSectionRing.sectionRingAlgebra pX hω
  let _ := TensorPowerSectionRing.commRing (R := X'.sheaf) (canonicalSheaf pX') (op ⊤)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 hω')
  let _ := TensorPowerSectionRing.sectionRingAlgebra pX' hω'
  -- The degree-zero map sends the unit section to the unit section, since `E` preserves `1`.
  have h1 : ψ 0 (TensorPowerSectionRing.oneSec (R := X.sheaf) (canonicalSheaf pX) (op ⊤)) =
      TensorPowerSectionRing.oneSec (R := X'.sheaf) (canonicalSheaf pX') (op ⊤) := by
    have h := hE 0 (TensorPowerSectionRing.oneSec (R := X.sheaf) (canonicalSheaf pX) (op ⊤))
    have h' : E 1 = 1 := map_one E
    exact DirectSum.of_injective (β := CanonicalSectionRing.Component pX') 0 (h.symm.trans h')
  -- Hence `E` commutes with the structure maps `k → R(X, K)` and `k → R(X', K')`.
  have halg : ∀ c : k, E (algebraMap k (CanonicalSectionRing pX) c) =
      algebraMap k (CanonicalSectionRing pX') c := by
    intro c
    change E (DirectSum.of _ 0 (c • (show GlobalSectionsOver pX
        (moduleSheafTensorPower (R := X.sheaf) 0 (canonicalSheaf pX)) from
          TensorPowerSectionRing.oneSec (R := X.sheaf) (canonicalSheaf pX) (op ⊤)))) =
      DirectSum.of _ 0 (c • (show GlobalSectionsOver pX'
        (moduleSheafTensorPower (R := X'.sheaf) 0 (canonicalSheaf pX')) from
          TensorPowerSectionRing.oneSec (R := X'.sheaf) (canonicalSheaf pX') (op ⊤)))
    rw [hE, map_smul, h1]
  rw [kodairaDimension, kodairaDimension, (AlgEquiv.ofRingEquiv (f := E) halg).trdeg_eq]

end Hartshorne
