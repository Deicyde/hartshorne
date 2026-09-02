/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.AffineVariety
import Hartshorne.Projective.Variety

/-!
# Quasi-projective varieties are varieties

Hartshorne, *Algebraic Geometry*, I.3, the definition on p. 15.

The second of the four constructions the `Variety` structure demands, completing
the set: affine varieties are quasi-affine and projective varieties are
quasi-projective, so with `Variety.ofQuasiAffine` all four of Hartshorne's cases
are covered.

It runs parallel to the quasi-affine construction, with the equal-degree
condition carried along: the common denominator `h₁h₂` and numerator
`g₁h₂ + g₂h₁` are both homogeneous of degree `n₁ + n₂`, so the subalgebra
operations preserve it.

Restriction supplies the restricted point explicitly rather than as `_`. With a
metavariable the elaborator cannot match the two coercions syntactically and
diverges unfolding `eval`; see the note in the germ file.

## Main definitions

* `Hartshorne.projRegularSubalgebra`
* `Hartshorne.Variety.ofQuasiProjective`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (ProjectiveSpace k σ)}

/-- The map to projective space attached to an open subset of `Y`. -/
abbrev projOpenIota (U : Opens Y) : U → ProjectiveSpace k σ :=
  fun x => Subtype.val (Subtype.val x)

/-- The regular functions on an open subset of a subset of projective space, as
a `k`-subalgebra. -/
noncomputable def projRegularSubalgebra (U : Opens Y) :
    Subalgebra k (U → k) where
  carrier := {f | IsRegularProjVia (projOpenIota U) f}
  mul_mem' hf hg := IsRegularProjVia.mul hf hg
  one_mem' := isRegularProjVia_const _ 1
  add_mem' hf hg := IsRegularProjVia.add hf hg
  zero_mem' := isRegularProjVia_const _ 0
  algebraMap_mem' c := isRegularProjVia_const _ c

@[simp]
theorem mem_projRegularSubalgebra {U : Opens Y} {f : U → k} :
    f ∈ projRegularSubalgebra U ↔ IsRegularProjVia (projOpenIota U) f :=
  Iff.rfl

/-- Restriction of a regular function to a smaller open set stays regular. -/
theorem isRegularProjVia_restrict {U V : Opens Y} (hUV : V ≤ U) {f : U → k}
    (hf : IsRegularProjVia (projOpenIota U) f) :
    IsRegularProjVia (projOpenIota V) (fun x : V => f ⟨x.1, hUV x.2⟩) := by
  intro Q
  obtain ⟨W, hW, hQW, n, g, h, hg, hh, hne, he⟩ := hf ⟨Q.1, hUV Q.2⟩
  exact ⟨(fun x : V => (⟨x.1, hUV x.2⟩ : U)) ⁻¹' W,
    hW.preimage (Continuous.subtype_mk continuous_subtype_val _), hQW, n, g, h, hg, hh,
    fun x hx => hne ⟨x.1, hUV x.2⟩ hx, fun x hx => he ⟨x.1, hUV x.2⟩ hx⟩

/-- Irreducibility of the carrier. -/
theorem irreducibleSpace_of_isQuasiProjVariety (hY : IsQuasiProjVariety Y) :
    IrreducibleSpace Y := by
  have hne : Nonempty Y := hY.1.to_subtype
  haveI : PreirreducibleSpace Y :=
    isPreirreducible_iff_preirreducibleSpace.1 hY.isIrreducible.2
  exact ⟨hne⟩

/-- A quasi-projective variety, viewed as a `Variety`. -/
noncomputable def Variety.ofQuasiProjective (hY : IsQuasiProjVariety Y) : Variety k where
  carrier := Y
  irreducible := irreducibleSpace_of_isQuasiProjVariety hY
  regular := projRegularSubalgebra
  regular_restrict {U V} hUV {f} hf :=
    mem_projRegularSubalgebra.2
      (isRegularProjVia_restrict hUV (mem_projRegularSubalgebra.1 hf))

/-- A projective variety is in particular a variety. -/
noncomputable def Variety.ofProjective (hY : IsProjVariety Y) : Variety k :=
  Variety.ofQuasiProjective hY.isQuasiProjVariety

end Hartshorne
