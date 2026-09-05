/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyLocalRing
import Hartshorne.Morphism.LocalRingStructure

/-!
# The two constructions of `𝒪_P` agree on an affine variety

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(b) and (c).

`𝒪_P` was built twice: once in affine coordinates, which is what §3's affine
results are stated over, and once over the bundled `Variety`, which is what §3's
projective results need. For a quasi-affine `Y` the two are the same ring.

There is nothing to prove. A germ representative is an open neighbourhood of `P`
carrying a regular function, and "regular" on `Variety.ofQuasiAffine hY` is by
definition `IsRegularVia` in the affine coordinates; the only difference is that
one side packages the neighbourhood as `Set Y` plus a proof and the other as
`Opens Y`. The equivalence relation is the same condition on both sides, so the
quotients are the same, and the ring operations are given by the same formulas
on representatives.

The file exists because that "nothing" still has to be written down: the two
types are not definitionally equal, and Theorem 3.4(b) has to cross between
them to reach Theorem 3.2(c).

## Main definitions

* `Hartshorne.localRingEquivAffine`
-/

namespace Hartshorne

open TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)}
  (hY : IsQuasiAffineVariety Y)

variable {P : (Variety.ofQuasiAffine hY).carrier}

/-- The same point, spelled so that the affine instances are found. Instance
search will not unfold `Variety.ofQuasiAffine` to see that its carrier is `↥Y`,
and `⟨P.1, P.2⟩` is `P` by eta. -/
abbrev affinePoint (P : (Variety.ofQuasiAffine hY).carrier) : Y := ⟨P.1, P.2⟩

/-- An affine germ representative, as a representative over the bundled
variety. -/
def germRepToVariety (r : GermRep Y (affinePoint hY P)) :
    Variety.GermRep (Variety.ofQuasiAffine hY) P where
  U := ⟨r.U, r.isOpen_U⟩
  mem_U := r.mem_U
  toFun := r.toFun
  regular := r.isRegular

/-- And back again. -/
def germRepOfVariety (r : Variety.GermRep (Variety.ofQuasiAffine hY) P) :
    GermRep Y (affinePoint hY P) where
  U := (r.U : Set (Variety.ofQuasiAffine hY).carrier)
  isOpen_U := r.U.isOpen
  mem_U := r.mem_U
  toFun := r.toFun
  isRegular := r.regular

/-- **The abstract `𝒪_P` is the affine `𝒪_P`.**

Both sides are the quotient of the same representatives by the same relation,
with the same operations; the equivalence just repackages the neighbourhood. -/
noncomputable def localRingEquivAffine (P : (Variety.ofQuasiAffine hY).carrier) :
    Variety.LocalRingAt (Variety.ofQuasiAffine hY) P
      ≃+* LocalRingAt hY.isIrreducible (affinePoint hY P) where
  toFun := Quotient.map (germRepOfVariety hY) fun _ _ h => h
  invFun := Quotient.map (germRepToVariety hY) fun _ _ h => h
  left_inv := by
    refine Quotient.ind fun r => ?_
    exact Quotient.sound fun _ _ _ => rfl
  right_inv := by
    refine Quotient.ind fun r => ?_
    exact Quotient.sound fun _ _ _ => rfl
  map_mul' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl
  map_add' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl

@[simp]
theorem localRingEquivAffine_mk (P : (Variety.ofQuasiAffine hY).carrier)
    (r : Variety.GermRep (Variety.ofQuasiAffine hY) P) :
    localRingEquivAffine hY P (Quotient.mk (Variety.germSetoid _ P) r)
      = Quotient.mk (germSetoid hY.isIrreducible _) (germRepOfVariety hY r) :=
  rfl

end Hartshorne
