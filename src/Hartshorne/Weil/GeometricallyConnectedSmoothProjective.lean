/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceOverScheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Smooth projective geometrically connected schemes over a finite field

Hartshorne, *Algebraic Geometry*, Appendix C, §1 (p. 450): the hypotheses under which the Weil
assertions are stated.

`Hartshorne.IsSmoothProjectiveGeometricallyConnected k f n` says that the scheme
`f : X ⟶ Spec k` over the finite field `k = 𝔽_q` is
* smooth of pure dimension `n`: `f` is smooth of relative dimension `n`;
* projective (`Hartshorne.Projective`);
* geometrically connected: the base extension `X ×_{Spec k} Spec k̄` of `X` to the algebraic
  closure `k̄ = AlgebraicClosure k` is connected (in particular nonempty).
-/

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

universe u

/-- **Smooth projective geometrically connected schemes over a finite field** (Hartshorne,
Appendix C, §1, p. 450, the hypotheses of the Weil assertions). For a finite field `k` and a
scheme `f : X ⟶ Spec k`: `X` is smooth over `k` of pure dimension `n` (`f` is smooth of relative
dimension `n`), projective over `k`, and its base extension to an algebraic closure of `k` is
connected. -/
structure IsSmoothProjectiveGeometricallyConnected (k : Type u) [Field k] [Finite k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) : Prop where
  /-- `X` is smooth over `k` of pure dimension `n`. -/
  smoothOfRelativeDimension : SmoothOfRelativeDimension n f
  /-- `X` is projective over `k`. -/
  projective : Hartshorne.Projective f
  /-- The base extension of `X` to an algebraic closure of `k` is connected. -/
  connectedSpace_baseExtension : ConnectedSpace
    (baseExtension f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))

end Hartshorne
