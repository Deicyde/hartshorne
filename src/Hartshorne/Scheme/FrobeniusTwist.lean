/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Over

/-!
# Absolute Frobenius and Hartshorne's Frobenius twist

Hartshorne, *Algebraic Geometry*, IV.2, pp. 301--302.

For a scheme whose local rings have characteristic `p`, the absolute Frobenius is the identity on
points and raises local sections to their `p`th powers. If `X` is a scheme over a field `k`, then
Hartshorne's `X^p` has the same underlying scheme and structure map obtained by following the old
structure map by Frobenius on `Spec k`. With this convention absolute Frobenius has the
source-facing orientation `X^p ⟶ X` as a `k`-morphism.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- A scheme is of characteristic `p` when all of its local rings are of characteristic `p`. -/
class IsCharP (X : Scheme.{u}) (p : ℕ) : Prop where
  charP_stalk (x : X) : CharP (X.presheaf.stalk x) p

section AbsoluteFrobenius

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] [X.IsCharP p]
include p

/-- The `p`th-power endomorphism of the ring of sections over an open set. -/
private def frobeniusApp (U : X.Opens) : Γ(X, U) →+* Γ(X, U) where
  toFun s := s ^ p
  map_one' := one_pow p
  map_mul' _ _ := mul_pow ..
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' s t := by
    apply TopCat.Presheaf.section_ext X.sheaf U
    intro x hx
    let _ : CharP (X.presheaf.stalk x) p := IsCharP.charP_stalk x
    calc
      X.presheaf.germ U x hx ((s + t) ^ p) =
          (X.presheaf.germ U x hx (s + t)) ^ p := map_pow _ _ _
      _ = (X.presheaf.germ U x hx s + X.presheaf.germ U x hx t) ^ p := by rw [map_add]
      _ = (X.presheaf.germ U x hx s) ^ p + (X.presheaf.germ U x hx t) ^ p :=
        add_pow_expChar _ _ p
      _ = X.presheaf.germ U x hx (s ^ p) + X.presheaf.germ U x hx (t ^ p) := by
        rw [map_pow, map_pow]
      _ = X.presheaf.germ U x hx (s ^ p + t ^ p) := (map_add _ _ _).symm

/-- The `p`th-power natural endomorphism of the structure presheaf. -/
private def frobeniusNatTrans : X.presheaf ⟶ X.presheaf where
  app U := CommRingCat.ofHom (frobeniusApp X p U.unop)
  naturality U V f := by
    ext s
    exact (map_pow (X.presheaf.map f).hom s p).symm

/-- Absolute Frobenius before verifying localness on stalks. -/
private def absoluteFrobeniusPresheafed :
    X.toPresheafedSpace.Hom X.toPresheafedSpace where
  base := TopCat.ofHom ⟨id, continuous_id⟩
  c := frobeniusNatTrans X p

set_option backward.isDefEq.respectTransparency false in
private theorem absoluteFrobeniusPresheafed_stalkMap_germ_apply
    (U : X.Opens) (x : X) (hx : (absoluteFrobeniusPresheafed X p).base x ∈ U)
    (s : Γ(X, U)) :
    (absoluteFrobeniusPresheafed X p).stalkMap x
        (X.presheaf.germ U ((absoluteFrobeniusPresheafed X p).base x) hx s) =
      X.presheaf.germ U x (by simpa [absoluteFrobeniusPresheafed] using hx) (s ^ p) := by
  rw [PresheafedSpace.stalkMap_germ_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Absolute Frobenius as a morphism of locally ringed spaces. -/
private def absoluteFrobeniusLRS :
    X.toLocallyRingedSpace ⟶ X.toLocallyRingedSpace :=
  LocallyRingedSpace.Hom.mk (absoluteFrobeniusPresheafed X p) fun x ↦
    IsLocalHom.mk fun a ha ↦ by
      obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
      rw [absoluteFrobeniusPresheafed_stalkMap_germ_apply X p U x hx s] at ha
      have hpow : IsUnit ((X.presheaf.germ U x
          (by simpa [absoluteFrobeniusPresheafed] using hx) s) ^ p) := by
        simpa only [map_pow] using ha
      have hu := (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp hpow
      simpa [absoluteFrobeniusPresheafed] using hu

/-- **Absolute Frobenius.** It is the identity on points and raises sections to their `p`th
powers. -/
def absoluteFrobenius : X ⟶ X :=
  Scheme.Hom.mk (absoluteFrobeniusLRS X p)

@[simp]
theorem absoluteFrobenius_apply (x : X) : X.absoluteFrobenius p x = x := rfl

@[simp]
theorem absoluteFrobenius_app (U : X.Opens) (s : Γ(X, U)) :
    (X.absoluteFrobenius p).app U s = s ^ p := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem absoluteFrobenius_stalkMap_apply (x : X) (a : X.presheaf.stalk x) :
    (X.absoluteFrobenius p).stalkMap x a = a ^ p := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  change (absoluteFrobeniusPresheafed X p).stalkMap x
    (X.presheaf.germ U x hx s) = (X.presheaf.germ U x hx s) ^ p
  let hx' : (absoluteFrobeniusPresheafed X p).base x ∈ U := by
    simpa [absoluteFrobeniusPresheafed] using hx
  have hgerm : X.presheaf.germ U ((absoluteFrobeniusPresheafed X p).base x) hx' s =
      X.presheaf.germ U x hx s := by
    congr
  conv_lhs => rw [← hgerm]
  rw [absoluteFrobeniusPresheafed_stalkMap_germ_apply X p U x hx' s]
  exact map_pow (X.presheaf.germ U x hx).hom s p

end AbsoluteFrobenius

/-- Frobenius on `Spec k`, induced contravariantly by the ring Frobenius of `k`. -/
def specFrobenius (p : ℕ) (k : Type u) [Field k] [CharP k p] [Fact p.Prime] :
    Spec (.of k) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (frobenius k p))

variable {p : ℕ}

/-- The displayed Frobenius square for a scheme over a field of characteristic `p`. -/
theorem absoluteFrobenius_comp_structureMap
    (k : Type u) [Field k] [CharP k p] [Fact p.Prime]
    (X : CategoryTheory.Over (Spec (.of k))) [X.left.IsCharP p] :
    X.left.absoluteFrobenius p ≫ X.hom = X.hom ≫ specFrobenius p k := by
  apply ext_to_Spec
  ext a
  change (X.hom.appTop ((Scheme.ΓSpecIso (.of k)).inv a)) ^ p =
    X.hom.appTop ((specFrobenius p k).appTop ((Scheme.ΓSpecIso (.of k)).inv a))
  have hspec := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (frobenius k p))) a
  change (Scheme.ΓSpecIso (.of k)).inv (a ^ p) =
    (specFrobenius p k).appTop ((Scheme.ΓSpecIso (.of k)).inv a) at hspec
  rw [← hspec]
  simp only [map_pow]

/-- Hartshorne's `X^p`: the same abstract scheme, with structural morphism followed by Frobenius
on `Spec k`. -/
def frobeniusTwist
    (k : Type u) [Field k] [CharP k p] [Fact p.Prime]
    (X : CategoryTheory.Over (Spec (.of k))) :
    CategoryTheory.Over (Spec (.of k)) :=
  Over.mk (X.hom ≫ specFrobenius p k)

@[simp]
theorem frobeniusTwist_left
    (k : Type u) [Field k] [CharP k p] [Fact p.Prime]
    (X : CategoryTheory.Over (Spec (.of k))) :
    (frobeniusTwist (p := p) k X).left = X.left := rfl

@[simp]
theorem frobeniusTwist_hom
    (k : Type u) [Field k] [CharP k p] [Fact p.Prime]
    (X : CategoryTheory.Over (Spec (.of k))) :
    (frobeniusTwist (p := p) k X).hom = X.hom ≫ specFrobenius p k := rfl

/-- Hartshorne's correctly oriented `k`-linear Frobenius `X^p ⟶ X`. Its underlying scheme map
is absolute Frobenius. -/
def frobeniusTwistTo
    (k : Type u) [Field k] [CharP k p] [Fact p.Prime]
    (X : CategoryTheory.Over (Spec (.of k))) [X.left.IsCharP p] :
    frobeniusTwist (p := p) k X ⟶ X :=
  Over.homMk (X.left.absoluteFrobenius p) (absoluteFrobenius_comp_structureMap k X)

@[simp]
theorem frobeniusTwistTo_left
    (k : Type u) [Field k] [CharP k p] [Fact p.Prime]
    (X : CategoryTheory.Over (Spec (.of k))) [X.left.IsCharP p] :
    (frobeniusTwistTo (p := p) k X).left = X.left.absoluteFrobenius p := rfl

end Scheme

end AlgebraicGeometry
