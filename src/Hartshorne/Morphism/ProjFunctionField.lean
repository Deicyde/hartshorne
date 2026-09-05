/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.AffineRationalCompare
import Hartshorne.Morphism.ChartIso
import Hartshorne.Morphism.OpenSubvarietyFunctionField

/-!
# The function field of a projective variety, on a chart

Hartshorne, *Algebraic Geometry*, I.3, the reduction step in Theorem 3.4(c)
(pp. 18-19).

For `Y` projective meeting the chart `Uᵢ`,

`K(Y) ≅ K(Yᵢ)`,

where `Yᵢ` is the affine variety `φᵢ(Y ∩ Uᵢ)`. Combined with Theorem 3.2(d),
which says `K(Yᵢ)` is the fraction field of `A(Yᵢ)`, this is what Hartshorne
means by reducing (c) to the affine case.

It is the same three-step chain as for local rings, and every step is shorter,
because a rational function has no base point:

* `K(Y) ≅ K(Y∩Uᵢ)`, since the function field does not see beyond a nonempty open
  subset;
* `K(Y∩Uᵢ) ≅ K(Yᵢ)` along the chart isomorphism;
* the abstract function field on `Yᵢ` is the affine one.

The germ chain needed a fourth step, and a nonemptiness hypothesis at the point;
here the only hypothesis is that `Y` meets the chart at all.

## Main definitions

* `Hartshorne.projFunctionFieldEquiv`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ] [DecidableEq σ]
  [Nonempty σ] {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y) (i : σ)
  (hne : (Y ∩ standardChart i).Nonempty)

/-- **The function field of a projective variety is that of an affine chart.**

Three isomorphisms: restrict to the chart piece, transport along the chart
isomorphism, and identify the abstract function field with the affine one. -/
noncomputable def projFunctionFieldEquiv :
    Variety.FunctionField (Variety.ofQuasiProjective hY.isQuasiProjVariety)
      ≃+* FunctionField
        (isQuasiAffineVariety_chartMap_image i hY.isQuasiProjVariety hne).isIrreducible :=
  let hYq := hY.isQuasiProjVariety
  let hYi := isQuasiProjVariety_inter_standardChart k i hYq hne
  let hW := isQuasiAffineVariety_chartMap_image i hYq hne
  let e₁ : Variety.FunctionField (Variety.ofQuasiProjective hYq)
      ≃+* Variety.FunctionField (Variety.ofQuasiProjective hYi) :=
    RingEquiv.ofBijective
      ((inclHom hYq hYi Set.inter_subset_left).functionFieldHom
        (dense_range_inclHom hYq hYi Set.inter_subset_left
          (isOpen_inter_standardChart_in k i)))
      (bijective_functionFieldHom_inclHom hYq hYi Set.inter_subset_left
        (isOpen_inter_standardChart_in k i))
  let e₂ : Variety.FunctionField (chartTarget k i hYq hne)
      ≃+* Variety.FunctionField (Variety.ofQuasiProjective hYi) :=
    RingEquiv.ofBijective
      ((chartHom k i hYq hne).functionFieldHom
        (VarietyHom.dense_range_of_surjective (isIso_chartHom k i hYq hne).bijective.2))
      (VarietyHom.bijective_functionFieldHom_of_isIso (isIso_chartHom k i hYq hne) _)
  let e₃ := functionFieldEquivAffine hW
  (e₁.trans e₂.symm).trans e₃

end Hartshorne
