/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.Flatness.LocalizationFlatModuleOverBase
import Hartshorne.Cohomology.Flatness.ModuleSheafFlatOverBase
import Hartshorne.Scheme.AffineTildeLocalization

/-!
# Flatness of an affine associated sheaf

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.2(d) (p. 254).

For a ring map `A ⟶ B` and a `B`-module `M`, the associated module sheaf `M̃` on
`Spec B` is flat over `Spec A` precisely when `M`, restricted to `A`, is flat.
-/

open CategoryTheory

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

private theorem affineTildeStalk_flat_iff_flatOverAt
    {A B : CommRingCat.{u}} (f : A ⟶ B) (M : ModuleCat.{u} B)
    (p : PrimeSpectrum B) :
    letI : Module B ((tilde M).presheaf.stalk p) :=
      tilde.instModuleCarrierCarrierStalkAbPresheaf M p
    letI : Module A ((tilde M).presheaf.stalk p) :=
      Module.compHom ((tilde M).presheaf.stalk p) f.hom
    Module.Flat A ((tilde M).presheaf.stalk p) ↔
      (tilde M).FlatOverAt (Spec.map f) p := by
  let q := PrimeSpectrum.comap f.hom p
  let St := (tilde M).presheaf.stalk p
  let FX : _root_.PresheafOfModules.{u}
      ((Spec B).presheaf ⋙ forget₂ CommRingCat RingCat) := (tilde M).val
  let _ : Algebra A B := f.hom.toAlgebra
  let _ : Module B St :=
    StructureSheaf.instModuleCarrierStalkAbPresheafOpensCarrierTopModuleStructurePresheaf p
  let _ : Module A St := Module.compHom St f.hom
  let _ : Algebra A ((Spec A).presheaf.stalk q) := StructureSheaf.stalkAlgebra A q
  let _ : IsLocalization q.asIdeal.primeCompl ((Spec A).presheaf.stalk q) :=
    StructureSheaf.IsLocalization.to_stalk A q
  let _ : Algebra B ((Spec B).presheaf.stalk p) := StructureSheaf.stalkAlgebra B p
  let _ : Module ((Spec B).presheaf.stalk p) St :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier FX p
  let _ : IsScalarTower B ((Spec B).presheaf.stalk p) St :=
    StructureSheaf.instIsScalarTowerCarrierStalkCommRingCatStructurePresheafInCommRingCatCarrierAbPresheafOpensCarrierTopModuleStructurePresheaf
      p
  let _ : Module ((Spec A).presheaf.stalk q) St :=
    Module.compHom St ((Spec.map f).stalkMap p).hom
  let _ : IsScalarTower A ((Spec A).presheaf.stalk q) St :=
    IsScalarTower.of_algebraMap_smul fun a m => by
      change ((Spec.map f).stalkMap p)
        (StructureSheaf.toStalk A q a) • m = f a • m
      have ha := congr($(stalkMap_toStalk f p) a)
      change ((Spec.map f).stalkMap p)
          (StructureSheaf.toStalk A q a) = StructureSheaf.toStalk B p (f a) at ha
      rw [ha]
      exact IsScalarTower.algebraMap_smul B (f a) m
  exact (Module.flat_iff_of_isLocalization
    ((Spec A).presheaf.stalk q) q.asIdeal.primeCompl St).symm

/-- **Hartshorne III.9, Proposition 9.2(d).** For `f : A ⟶ B` and a `B`-module
`M`, the associated module sheaf `M̃` on `Spec B` is flat over `Spec A` if and only if
`M`, restricted along `f`, is flat over `A`. -/
theorem affineTilde_flatOver_iff_module_flat
    {A B : CommRingCat.{u}} (f : A ⟶ B) (M : ModuleCat.{u} B) :
    letI : Module A M := Module.compHom M f.hom
    (tilde M).FlatOver (Spec.map f) ↔ Module.Flat A M := by
  let _ : Algebra A B := f.hom.toAlgebra
  let _ : Module A M := Module.compHom M f.hom
  let _ : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  constructor
  · intro h
    apply Module.flat_of_isLocalized_maximal B M
      (fun P => LocalizedModule P.primeCompl M)
      (fun P => LocalizedModule.mkLinearMap P.primeCompl M)
    intro P hP
    let p : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    let _ : p.asIdeal.IsPrime := p.isPrime
    let St := (tilde M).presheaf.stalk p
    let _ : Module B St := tilde.instModuleCarrierCarrierStalkAbPresheaf M p
    let _ : Module A St := Module.compHom St f.hom
    let _ : IsScalarTower A B St := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hp : Module.Flat A St := (affineTildeStalk_flat_iff_flatOverAt f M p).2 (h p)
    let e := affineTildeStalkIso M p
    exact (Module.Flat.equiv_iff (e.restrictScalars A)).2 hp
  · intro h p
    let _ : p.asIdeal.IsPrime := p.isPrime
    let St := (tilde M).presheaf.stalk p
    let _ : Module B St := tilde.instModuleCarrierCarrierStalkAbPresheaf M p
    let _ : Module A St := Module.compHom St f.hom
    let _ : IsScalarTower A B St := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    apply (affineTildeStalk_flat_iff_flatOverAt f M p).1
    let _ : Module.Flat A M := h
    let e := affineTildeStalkIso M p
    exact (Module.Flat.equiv_iff (e.restrictScalars A)).1
      (localizedModule_flat_over_base p.asIdeal.primeCompl)

end

end Hartshorne
