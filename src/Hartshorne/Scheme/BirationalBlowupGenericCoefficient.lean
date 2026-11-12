/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SectionAlgebraMultiplicative
import Hartshorne.Scheme.AmpleSectionsAffineBasis
import Hartshorne.Scheme.Differentials.CanonicalPullback

/-!
# Sections of an invertible sheaf as rational functions

Hartshorne, *Algebraic Geometry*, II, proof of Theorem 7.17, Steps 4–5 (pp. 167–168): the graded
pieces of the section algebra of a birational projective morphism are viewed inside the function
field.

Let `Z` be an integral scheme with generic point `η` and `F` an `𝒪_Z`-module with a trivializing
section `e` over an open `W ∋ η`. A section `x` of `F` over an open `O ∋ η` restricts on `O ∩ W`
to `a • e` for a unique function `a`, and its *generic coefficient* is the germ of `a` at `η`, an
element of the function field `K(Z)` (`Hartshorne.GenericCoefficient.genericCoeff`). It is
additive, sends `c • x` to `c · coeff(x)`, and is compatible with restriction; it is injective
when sections of `F` are determined on a nonempty open, for instance when `F` is invertible
(`genericCoeff_injective`).

For an invertible sheaf `L` with trivializing section `e` over `W ∋ η`, the tensor powers `L^{n}`
are trivialized by `e ⊗ ⋯ ⊗ e`, and the generic coefficients turn the products
`L^{p} × L^{q} → L^{p+q}` into multiplication in `K(Z)` (`genericCoeff_mulSection`).
-/

universe u

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Hartshorne

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace GenericCoefficient

variable {Z : Scheme.{u}} {F : Z.Modules} {W : Z.Opens} {e : Γ(F, W)}

/-- The coefficient of a section `x` over `V ⊆ W` with respect to a trivializing section `e`:
the unique function `a` with `x = a • e|_V`. -/
def frameCoeff (he : IsTrivializingSection F W e) {V : Z.Opens} (h : V ≤ W) (x : Γ(F, V)) :
    Γ(Z, V) :=
  Function.surjInv (he V h).2 x

theorem frameCoeff_smul (he : IsTrivializingSection F W e) {V : Z.Opens} (h : V ≤ W)
    (x : Γ(F, V)) : frameCoeff he h x • F.presheaf.map (homOfLE h).op e = x :=
  Function.surjInv_eq (he V h).2 x

theorem frameCoeff_eq (he : IsTrivializingSection F W e) {V : Z.Opens} (h : V ≤ W)
    {x : Γ(F, V)} {a : Γ(Z, V)} (ha : a • F.presheaf.map (homOfLE h).op e = x) :
    frameCoeff he h x = a :=
  (he V h).1 ((frameCoeff_smul he h x).trans ha.symm)

theorem frameCoeff_add (he : IsTrivializingSection F W e) {V : Z.Opens} (h : V ≤ W)
    (x y : Γ(F, V)) : frameCoeff he h (x + y) = frameCoeff he h x + frameCoeff he h y :=
  frameCoeff_eq he h (by rw [add_smul, frameCoeff_smul, frameCoeff_smul])

theorem frameCoeff_smul_left (he : IsTrivializingSection F W e) {V : Z.Opens} (h : V ≤ W)
    (c : Γ(Z, V)) (x : Γ(F, V)) : frameCoeff he h (c • x) = c * frameCoeff he h x :=
  frameCoeff_eq he h (by rw [mul_smul, frameCoeff_smul])

theorem frameCoeff_map (he : IsTrivializingSection F W e) {V V' : Z.Opens} (h : V ≤ W)
    (h' : V' ≤ V) (x : Γ(F, V)) :
    frameCoeff he (h'.trans h) (F.presheaf.map (homOfLE h').op x) =
      Z.presheaf.map (homOfLE h').op (frameCoeff he h x) := by
  refine frameCoeff_eq he _ ?_
  conv_rhs => rw [← frameCoeff_smul he h x]
  rw [Scheme.Modules.map_smul, Scheme.Modules.map_map_homOfLE]

variable [IsIntegral Z] (he : IsTrivializingSection F W e) (hW : genericPoint Z ∈ W)

/-- **The generic coefficient** of a section `x` of `F` over an open `O ∋ η`: the germ at the
generic point of the coefficient of `x|_{O ∩ W}` with respect to the trivializing section `e`. -/
def genericCoeff {O : Z.Opens} (hO : genericPoint Z ∈ O) (x : Γ(F, O)) : Z.functionField :=
  Z.presheaf.germ (O ⊓ W) (genericPoint Z) ⟨hO, hW⟩
    (frameCoeff he inf_le_right (F.presheaf.map (homOfLE inf_le_left).op x))

theorem genericCoeff_add {O : Z.Opens} (hO : genericPoint Z ∈ O) (x y : Γ(F, O)) :
    genericCoeff he hW hO (x + y) = genericCoeff he hW hO x + genericCoeff he hW hO y := by
  rw [genericCoeff, genericCoeff, genericCoeff, map_add, frameCoeff_add, map_add]

theorem genericCoeff_zero {O : Z.Opens} (hO : genericPoint Z ∈ O) :
    genericCoeff he hW hO (0 : Γ(F, O)) = 0 := by
  have := genericCoeff_add he hW hO 0 0
  rw [add_zero] at this
  exact (add_eq_left.mp this.symm)

theorem genericCoeff_smul {O : Z.Opens} (hO : genericPoint Z ∈ O) (c : Γ(Z, O))
    (x : Γ(F, O)) :
    genericCoeff he hW hO (c • x) =
      Z.presheaf.germ O (genericPoint Z) hO c * genericCoeff he hW hO x := by
  rw [genericCoeff, genericCoeff, Scheme.Modules.map_smul, frameCoeff_smul_left, map_mul,
    TopCat.Presheaf.germ_res_apply]

theorem genericCoeff_map {O O' : Z.Opens} (h : O' ≤ O) (hO' : genericPoint Z ∈ O')
    (x : Γ(F, O)) :
    genericCoeff he hW hO' (F.presheaf.map (homOfLE h).op x) =
      genericCoeff he hW (h hO') x := by
  have hle : O' ⊓ W ≤ O ⊓ W := inf_le_inf_right W h
  rw [genericCoeff, genericCoeff, Scheme.Modules.map_map_homOfLE]
  have key := frameCoeff_map he (inf_le_right : O ⊓ W ≤ W) hle
    (F.presheaf.map (homOfLE (inf_le_left : O ⊓ W ≤ O)).op x)
  rw [Scheme.Modules.map_map_homOfLE] at key
  rw [key, TopCat.Presheaf.germ_res_apply]

/-- The generic coefficient is injective as soon as sections of `F` over `O` are determined on
`O ∩ W`. -/
theorem genericCoeff_injective {O : Z.Opens} (hO : genericPoint Z ∈ O)
    (hinj : Function.Injective (F.presheaf.map (homOfLE (inf_le_left : O ⊓ W ≤ O)).op)) :
    Function.Injective (genericCoeff he hW hO) := by
  intro x y hxy
  apply hinj
  rw [← frameCoeff_smul he (inf_le_right : O ⊓ W ≤ W) (F.presheaf.map _ x),
    ← frameCoeff_smul he (inf_le_right : O ⊓ W ≤ W) (F.presheaf.map _ y)]
  exact congrArg (· • _) (germ_injective_of_isIntegral Z (U := O ⊓ W) (genericPoint Z) ⟨hO, hW⟩ hxy)

/-- On an integral scheme the generic coefficient of a section of an invertible sheaf is
injective. -/
theorem genericCoeff_injective_of_isInvertible (hF : F.IsInvertible)
    {O : Z.Opens} (hO : genericPoint Z ∈ O) : Function.Injective (genericCoeff he hW hO) := by
  have : Nonempty (O ⊓ W : Z.Opens) := ⟨⟨_, hO, hW⟩⟩
  exact genericCoeff_injective he hW hO
    (Scheme.Modules.presheaf_map_injective_of_isInvertible hF inf_le_left)

end GenericCoefficient

/-! ### Tensor powers -/

namespace GenericCoefficient

variable {Z : Scheme.{u}} {L : Z.Modules} {W : Z.Opens} {e : Γ(L, W)}

/-- The `n`-th tensor power `e ⊗ ⋯ ⊗ e` of a section `e` of `L`. -/
abbrev framePow (e : Γ(L, W)) (n : ℕ) : Γ(moduleSheafTensorPower n L, W) :=
  (moduleSheafTensorPowerMultilinear n L).app (op W) (fun _ => e)

theorem framePow_map {V : Z.Opens} (h : V ≤ W) (n : ℕ) :
    (Scheme.Modules.presheaf (X := Z) (moduleSheafTensorPower n L)).map (homOfLE h).op
        (framePow e n) = framePow (L.presheaf.map (homOfLE h).op e) n :=
  (moduleSheafTensorPowerMultilinear n L).naturality (homOfLE h).op _

theorem mulSection_map {p q : ℕ} {V V' : Z.Opens} (h : V' ≤ V)
    (s : Γ(moduleSheafTensorPower p L, V)) (t : Γ(moduleSheafTensorPower q L, V)) :
    (Scheme.Modules.presheaf (X := Z) (moduleSheafTensorPower (p + q) L)).map (homOfLE h).op
        (Ringed.moduleSheafTensorPowerMulSection (R := Z.sheaf) s t) =
      Ringed.moduleSheafTensorPowerMulSection (R := Z.sheaf)
        ((Scheme.Modules.presheaf (X := Z) (moduleSheafTensorPower p L)).map (homOfLE h).op s)
        ((Scheme.Modules.presheaf (X := Z) (moduleSheafTensorPower q L)).map (homOfLE h).op t) :=
  Ringed.moduleSheafTensorPowerMulSection_restrict (R := Z.sheaf) h s t

theorem mulSection_smul_smul {p q : ℕ} {V : Z.Opens} (a b : Γ(Z, V))
    (s : Γ(moduleSheafTensorPower p L, V)) (t : Γ(moduleSheafTensorPower q L, V)) :
    Ringed.moduleSheafTensorPowerMulSection (R := Z.sheaf) (a • s) (b • t) =
      (a * b) • Ringed.moduleSheafTensorPowerMulSection (R := Z.sheaf) s t :=
  (Ringed.moduleSheafTensorPowerMulSection_smul_left (R := Z.sheaf)
    (show (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V) from a) s (b • t)).trans
    ((congrArg (a • ·) (Ringed.moduleSheafTensorPowerMulSection_smul_right (R := Z.sheaf)
      (show (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V) from b) s t)).trans
      (smul_smul a b _))

theorem mulSection_framePow {V : Z.Opens} (x : Γ(L, V)) (p q : ℕ) :
    Ringed.moduleSheafTensorPowerMulSection (R := Z.sheaf) (framePow x p) (framePow x q) =
      framePow x (p + q) := by
  refine (Ringed.moduleSheafTensorPowerMulSection_tprod (R := Z.sheaf) _ _).trans ?_
  congr 1
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

variable [IsIntegral Z] (he : IsTrivializingSection L W e) (hW : genericPoint Z ∈ W)

/-- **Products of sections of tensor powers** become products of generic coefficients:
`coeff(s · t) = coeff(s) · coeff(t)` for `s ∈ Γ(O, L^{p})`, `t ∈ Γ(O, L^{q})`. -/
theorem genericCoeff_mulSection {p q : ℕ} {O : Z.Opens} (hO : genericPoint Z ∈ O)
    (s : Γ(moduleSheafTensorPower p L, O)) (t : Γ(moduleSheafTensorPower q L, O)) :
    genericCoeff (he.moduleSheafTensorPower (p + q)) hW hO
        (Ringed.moduleSheafTensorPowerMulSection (R := Z.sheaf) s t) =
      genericCoeff (he.moduleSheafTensorPower p) hW hO s *
        genericCoeff (he.moduleSheafTensorPower q) hW hO t := by
  rw [genericCoeff, genericCoeff, genericCoeff, ← map_mul]
  congr 1
  refine frameCoeff_eq _ _ ?_
  have hs := frameCoeff_smul (he.moduleSheafTensorPower p) (inf_le_right : O ⊓ W ≤ W)
    ((Scheme.Modules.presheaf (X := Z) (moduleSheafTensorPower p L)).map
      (homOfLE (inf_le_left : O ⊓ W ≤ O)).op s)
  have ht := frameCoeff_smul (he.moduleSheafTensorPower q) (inf_le_right : O ⊓ W ≤ W)
    ((Scheme.Modules.presheaf (X := Z) (moduleSheafTensorPower q L)).map
      (homOfLE (inf_le_left : O ⊓ W ≤ O)).op t)
  rw [mulSection_map]
  conv_rhs => rw [← hs, ← ht]
  rw [mulSection_smul_smul, framePow_map, framePow_map, framePow_map, mulSection_framePow]

end GenericCoefficient

end Hartshorne
