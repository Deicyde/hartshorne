/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.CoordinateRingIso
import Hartshorne.Morphism.Hom

/-!
# Theorem 3.2(a) for the bundled variety

`Hartshorne.coordinateRingEquivGlobalRegular` identifies `A(Y)` with the regular
functions on `Y` as a subalgebra of `Y → k`. The bundled `Variety` indexes its
regular functions by open subsets, so `𝒪(Y)` there is a subalgebra of
`↥(⊤ : Opens Y) → k` instead. The two differ by the homeomorphism between a
space and its top open subset, and everything downstream — Corollary 3.7, the
equivalence of categories — wants the second form.

Rather than transport the whole of Theorem 3.2(a), the friction is isolated in
one general lemma: regularity is preserved by a homeomorphism that commutes with
the map to affine space. Applying it in both directions to the top open subset
converts between the two forms of `𝒪(Y)`.

## Main results

* `Hartshorne.IsRegularVia.comp_homeomorph`
* `Hartshorne.isRegular_iff_top`
* `Hartshorne.coordinateRingEquivRegularTop`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*}

/-- Regularity transports along a homeomorphism commuting with the map to affine
space: the representing quotient is pulled back unchanged, and only its
neighbourhood moves. -/
theorem IsRegularVia.comp_homeomorph {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {ι : B → (σ → k)} {f : B → k} (hf : IsRegularVia ι f) :
    IsRegularVia (fun a => ι (e a)) (fun a => f (e a)) := by
  intro P
  obtain ⟨U, hU, hPU, g, h, hne, he⟩ := hf (e P)
  exact ⟨e ⁻¹' U, hU.preimage e.continuous, hPU, g, h,
    fun x hx => hne (e x) hx, fun x hx => he (e x) hx⟩

variable {Y : Set (σ → k)}

/-- The two readings of "regular on all of `Y`" agree: as a function on `Y`, and
as a function on the top open subset of `Y`. -/
theorem isRegular_iff_top {f : Y → k} :
    IsRegular f ↔ IsRegularVia (openIota (⊤ : Opens Y)) fun z : (⊤ : Opens Y) => f z.1 :=
  ⟨fun hf => hf.comp_homeomorph (Homeomorph.Set.univ Y),
    fun hf => hf.comp_homeomorph (Homeomorph.Set.univ Y).symm⟩

variable [IsAlgClosed k] [Finite σ]

/-- **Theorem 3.2(a)** in the form the bundled `Variety` uses: `A(Y) ≅ 𝒪(Y)`,
with `𝒪(Y)` the regular functions on the top open subset. -/
noncomputable def coordinateRingEquivRegularTop (hY : IsAffineVariety Y) :
    coordinateRing Y ≃ₐ[k] (Variety.ofQuasiAffine hY.isQuasiAffineVariety).regular ⊤ :=
  AlgEquiv.ofBijective
    (AlgHom.codRestrict
      ((compAlgHom fun z : (⊤ : Opens Y) => z.1).comp (coordinateToRegular Y))
      ((Variety.ofQuasiAffine hY.isQuasiAffineVariety).regular ⊤)
      fun a => by
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact isRegularVia_eval (openIota (⊤ : Opens Y)) p)
    ⟨fun a b hab => by
      refine coordinateToRegular_injective (funext fun y => ?_)
      exact congrFun (congrArg Subtype.val hab) ⟨y, trivial⟩,
      fun g => by
        have hreg : IsRegular fun y : Y => g.val ⟨y, trivial⟩ := isRegular_iff_top.2 g.2
        obtain ⟨a, ha⟩ :=
          coordinateToRegular_surjective (IsAffineVariety.isIrreducible hY)
            (IsAffineVariety.isAlgebraicSet hY) hreg
        exact ⟨a, Subtype.ext (funext fun z => congrFun ha z.1)⟩⟩

end Hartshorne
