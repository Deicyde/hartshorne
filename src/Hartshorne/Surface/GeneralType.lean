/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.KodairaDimension
import Hartshorne.Surface.SurfaceCurveConvention

/-!
# Surfaces of general type

Hartshorne, *Algebraic Geometry*, V.6, definition following Theorem 6.5 (p. 422).

A Chapter V surface `X` (`Hartshorne.Surface`) is *of general type* when its Kodaira dimension
`κ(X) = trdeg_k R(X, K) - 1` is maximal, namely equal to the dimension two of `X`
(`Hartshorne.Surface.IsGeneralType`). The value two is indeed the largest possible one:
`κ(X) ≤ 2` for every surface (`Hartshorne.Surface.kodairaDimension_le_two`).

## Main definitions and results

* `Hartshorne.Surface.canonicalSheaf_isInvertible`: the canonical sheaf of a surface is
  invertible, so its Kodaira dimension is defined.
* `Hartshorne.Surface.IsGeneralType`: `κ(X) = 2`.
* `Hartshorne.Surface.kodairaDimension_le_two`: `κ(X) ≤ 2`.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace Hartshorne

namespace Surface

universe u

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Surface k)

/-- The canonical sheaf `ω_X` of a surface `X` is invertible, because `X` is nonsingular of
dimension two over the algebraically closed field `k`. -/
theorem canonicalSheaf_isInvertible : (canonicalSheaf S.hom).IsInvertible :=
  Hartshorne.canonicalSheaf_isInvertible S.hom S.finiteType S.isRegular 2 S.dim_eq

/-- **A surface of general type** (Hartshorne V.6, p. 422): a surface `X` whose Kodaira dimension
is maximal, namely equal to its dimension two, `κ(X) = 2`. That two is the largest value of `κ` on
surfaces is `Hartshorne.Surface.kodairaDimension_le_two`. -/
def IsGeneralType : Prop :=
  kodairaDimension S.hom S.canonicalSheaf_isInvertible = 2

/-- **The Kodaira dimension of a surface is at most two**, so the value `κ(X) = 2` defining
surfaces of general type (Hartshorne V.6, p. 422) is the maximal one: the transcendence degree of
the canonical section ring of `X` over `k` is at most `dim X + 1 = 3`. -/
theorem kodairaDimension_le_two : kodairaDimension S.hom S.canonicalSheaf_isInvertible ≤ 2 := by
  have hω := S.canonicalSheaf_isInvertible
  let _ := TensorPowerSectionRing.commRing (R := S.X.sheaf) (canonicalSheaf S.hom) (op ⊤)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 hω)
  let _ := TensorPowerSectionRing.sectionRingAlgebra S.hom hω
  have hle : Algebra.trdeg k (CanonicalSectionRing S.hom) ≤ (2 : ℕ) + 1 :=
    TensorPowerSectionRing.trdeg_le S.hom S.finiteType hω (d := 2) S.dim_eq
  have h3 : ((2 : ℕ) + 1 : Cardinal) = (3 : ℕ) := by norm_num
  rw [h3] at hle
  have hnat : (Algebra.trdeg k (CanonicalSectionRing S.hom)).toNat ≤ 3 := by
    simpa using Cardinal.toNat_le_toNat hle (Cardinal.natCast_lt_aleph0)
  rw [kodairaDimension]
  omega

end Surface

end Hartshorne
