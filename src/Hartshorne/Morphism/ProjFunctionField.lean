/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.AffineRationalCompare
import Hartshorne.Morphism.ChartIso
import Hartshorne.Morphism.OpenSubvarietyFunctionField
import Hartshorne.Morphism.FunctionFieldFractions

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

* `Hartshorne.projFunctionFieldEquiv`,
  `Hartshorne.projFunctionFieldEquivFractionRing`
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


/-- **`K(Y)` is the fraction field of the coordinate ring of a chart.**

Theorem 3.4(c) in the form Hartshorne's reduction actually delivers: the
projective function field is the affine one, and the affine one is a fraction
field by Theorem 3.2(d). Rewriting the right-hand side as a graded localisation
of `S(Y)` is the step that remains.

Stated as an equivalence with `FractionRing` rather than as an `IsFractionRing`
instance, because the projective side carries no `A(Yᵢ)`-algebra structure and
inventing one would be a choice rather than a fact. -/
noncomputable def projFunctionFieldEquivFractionRing :
    Variety.FunctionField (Variety.ofQuasiProjective hY.isQuasiProjVariety)
      ≃+* FractionRing (coordinateRing (chartMap i '' (Y ∩ standardChart i))) :=
  let hW' := isAffineVariety_chartMap_image i hY hne
  have _ : IsDomain (coordinateRing (chartMap i '' (Y ∩ standardChart i))) :=
    isDomain_coordinateRing hW'
  have _ : IsFractionRing (coordinateRing (chartMap i '' (Y ∩ standardChart i)))
      (FunctionField (isQuasiAffineVariety_chartMap_image i hY.isQuasiProjVariety
        hne).isIrreducible) := isFractionRing_functionField _
  (projFunctionFieldEquiv hY i hne).trans
    (IsLocalization.algEquiv
      (nonZeroDivisors (coordinateRing (chartMap i '' (Y ∩ standardChart i))))
      (FunctionField (isQuasiAffineVariety_chartMap_image i hY.isQuasiProjVariety
        hne).isIrreducible)
      (FractionRing (coordinateRing (chartMap i '' (Y ∩ standardChart i))))).toRingEquiv

end Hartshorne
