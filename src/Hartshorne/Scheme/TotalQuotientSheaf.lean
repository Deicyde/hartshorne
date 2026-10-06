/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.Sheafify

/-!
# The total quotient sheaf

Hartshorne, *Algebraic Geometry*, II.6 (p. 141).

For an arbitrary scheme, sections are localized at those elements whose germs are
non-zero-divisors at every point, and the resulting presheaf is sheafified. No reducedness or
integrality hypothesis is imposed.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

noncomputable section

private abbrev ringUnits : CommRingCat.{u} ⥤ CommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

namespace Scheme

/-- The presheaf obtained by inverting sections whose germs are non-zero-divisors at every
point. -/
noncomputable abbrev totalQuotientPresheaf (X : Scheme.{u}) :
    TopCat.Presheaf CommRingCat.{u} X :=
  X.sheaf.presheaf.totalQuotientPresheaf

noncomputable instance (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    Algebra (X.presheaf.obj U) (X.totalQuotientPresheaf.obj U) := by
  change Algebra (X.presheaf.obj U)
    (Localization ((X.presheaf.submonoidPresheafOfStalk
      (fun x ↦ nonZeroDivisors (X.presheaf.stalk x))).obj U))
  infer_instance

/-- The total quotient sheaf `K_X`, obtained by sheafifying the total quotient presheaf. -/
noncomputable def totalQuotientSheaf (X : Scheme.{u}) :
    TopCat.Sheaf CommRingCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
    X.totalQuotientPresheaf

/-- The canonical morphism `O_X ⟶ K_X`. -/
noncomputable def toTotalQuotientSheaf (X : Scheme.{u}) :
    X.sheaf ⟶ X.totalQuotientSheaf :=
  (sheafificationIso X.sheaf).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map
      X.sheaf.presheaf.toTotalQuotientPresheaf

instance totalQuotientSheaf_mono (X : Scheme.{u}) : Mono X.toTotalQuotientSheaf := by
  let e := sheafificationIso X.sheaf
  change Mono (e.hom ≫ _)
  let _ : Mono e.hom :=
    ({ retraction := e.inv, id := e.hom_inv_id } : SplitMono e.hom).mono
  let _ : Mono X.sheaf.presheaf.toTotalQuotientPresheaf :=
    TopCat.Presheaf.instMonoCommRingCatToTotalQuotientPresheafPresheaf X.sheaf
  apply mono_comp'
  · infer_instance
  · exact preserves_mono_of_preservesLimit _ _

/-- The sheaf of multiplicative units `O_X^*`. -/
noncomputable def structureUnitsSheaf (X : Scheme.{u}) :
    TopCat.Sheaf CommGrpCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) ringUnits).obj X.sheaf

/-- The sheaf of multiplicative units `K_X^*`. -/
noncomputable def totalQuotientUnitsSheaf (X : Scheme.{u}) :
    TopCat.Sheaf CommGrpCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) ringUnits).obj
    X.totalQuotientSheaf

/-- The map `O_X^* ⟶ K_X^*` induced by the structure-sheaf map. -/
noncomputable def structureUnitsToTotalQuotientUnits (X : Scheme.{u}) :
    X.structureUnitsSheaf ⟶ X.totalQuotientUnitsSheaf :=
  (sheafCompose (Opens.grothendieckTopology X) ringUnits).map
    X.toTotalQuotientSheaf

private theorem totalQuotientDenominators_eq_nonZeroDivisors
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    (X.presheaf.submonoidPresheafOfStalk
      (fun x ↦ nonZeroDivisors (X.presheaf.stalk x))).obj (.op U) =
        nonZeroDivisors Γ(X, U) := by
  let F : TopCat.Sheaf CommRingCat.{u} X := X.sheaf
  change (F.presheaf.submonoidPresheafOfStalk
    (fun x ↦ nonZeroDivisors (F.presheaf.stalk x))).obj (.op U) =
      nonZeroDivisors (F.presheaf.obj (.op U))
  ext s
  rw [TopCat.Presheaf.submonoidPresheafOfStalk_obj]
  simp only [Submonoid.mem_iInf, Submonoid.mem_comap]
  constructor
  · intro hs
    rw [mem_nonZeroDivisors_iff_left]
    intro t hst
    apply TopCat.Presheaf.section_ext F U t 0
    intro x hx
    rw [map_zero]
    apply (mem_nonZeroDivisors_iff_left.mp (hs ⟨x, hx⟩))
    simpa only [map_zero, ← map_mul] using congr(F.presheaf.germ U x hx $hst)
  · intro hs x
    let _ := hU.isLocalization_stalk x
    exact IsLocalization.nonZeroDivisors_le_comap
      (hU.primeIdealOf x).asIdeal.primeCompl (X.presheaf.stalk x) hs

/-- On an affine open, the corresponding value of the raw total quotient presheaf is a total
quotient ring of its ring of regular functions. This statement deliberately concerns the raw
presheaf, not sections of its sheafification. -/
theorem totalQuotientPresheaf_isFractionRing_of_isAffineOpen
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    IsFractionRing Γ(X, U) (X.totalQuotientPresheaf.obj (.op U)) := by
  change IsFractionRing Γ(X, U)
    (Localization ((X.presheaf.submonoidPresheafOfStalk
      (fun x ↦ nonZeroDivisors (X.presheaf.stalk x))).obj (.op U)))
  rw [totalQuotientDenominators_eq_nonZeroDivisors X U hU]
  infer_instance

end Scheme

end

end AlgebraicGeometry
