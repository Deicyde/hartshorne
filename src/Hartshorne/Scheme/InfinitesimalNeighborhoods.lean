/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ModuleIdealSheafData

/-!
# Infinitesimal neighbourhoods

Hartshorne, *Algebraic Geometry*, II.9, introductory discussion of formal neighbourhoods
(p. 190), and the definitions on p. 194.

Let `Y ↪ X` be a closed subscheme with quasi-coherent module ideal sheaf `I ⊆ 𝒪_X`. Following
Hartshorne, for `n ≥ 1` the infinitesimal neighbourhood `Y_n` is the closed subscheme of `X` cut
out by `I ^ n`, so that `Y_1 = Y`. The definition is made for every `n : ℕ`; at `n = 0` it is the
empty subscheme cut out by `I ^ 0 = 𝒪_X`, which the book does not consider.

* `Hartshorne.QuasicoherentIdealSubsheaf.pow`: the power `I ^ k`, taken in the ideal sheaf: the
  sections lying, near every point, in `I(V) ^ k` on an affine open `V`
  (`ArtinReesKernelSheaf.powSmul` applied to `𝒪_X`). It is again quasi-coherent.
* `Hartshorne.QuasicoherentIdealSubsheaf.ideal_pow`: on every affine open `U`,
  `Γ(U, I ^ k) = Γ(U, I) ^ k`; equivalently (`quasicoherentIdealSubsheafEquiv_pow`) the power
  corresponds to the power of Mathlib's affine ideal data.
* `Hartshorne.QuasicoherentIdealSubsheaf.infinitesimalNeighborhood I n` (`Y_n`) with its closed
  immersion `I.infinitesimalNeighborhoodι n` into `X`, whose ideal is `I ^ n`
  (`QuasicoherentIdealSubsheaf.ker_infinitesimalNeighborhoodι`,
  `QuasicoherentIdealSubsheaf.quasicoherentIdealSubsheafEquiv_symm_ker_infinitesimalNeighborhoodι`).
* `Hartshorne.infinitesimalNeighborhoodOneIso`: for a closed immersion `f : Y ⟶ X` with module
  ideal sheaf `I`, `Y_1 ≅ Y` over `X` (`infinitesimalNeighborhoodOneIso_hom_comp`).

The earlier shifted versions `Hartshorne.infinitesimalNeighborhood I n` (cut out by
`I ^ (n + 1)`), `Hartshorne.infinitesimalNeighborhoodι`,
`Hartshorne.ker_infinitesimalNeighborhoodι`,
`Hartshorne.quasicoherentIdealSubsheafEquiv_symm_ker_infinitesimalNeighborhoodι`,
`Hartshorne.infinitesimalNeighborhoodZeroIso` and its `_hom_comp` lemma are deprecated.

Hartshorne works over a Noetherian scheme `X`; the construction here uses no finiteness, so it is
stated for every scheme.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

universe u

open ArtinReesKernelSheaf

variable {X : Scheme.{u}}

namespace QuasicoherentIdealSubsheaf

/-- **The power `I ^ k` of a quasi-coherent ideal subsheaf**, taken in the ideal sheaf: the
sections of `𝒪_X` lying, near every point, in `I(V) ^ k` on an affine open `V`. It is
quasi-coherent (the product of an ideal sheaf with a submodule sheaf, here `𝒪_X` itself). -/
def pow (I : QuasicoherentIdealSubsheaf X) (k : ℕ) : QuasicoherentIdealSubsheaf X where
  carrier := powSmul (quasicoherentIdealSubsheafEquiv I) k ⊤
  isLocal := isLocal_powSmul _ k ⊤
  isQuasicoherent := by
    have := ClosedImmersionIdeal.isQuasicoherent_unit X
    have := isQuasicoherent_top (E := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    exact isQuasicoherent_powSmul _ k isLocal_top

instance : Pow (QuasicoherentIdealSubsheaf X) ℕ where
  pow := pow

lemma pow_eq (I : QuasicoherentIdealSubsheaf X) (k : ℕ) : I ^ k = I.pow k := rfl

/-- **Powers agree with powers of the affine ideals.** On every affine open `U`, the sections of
`I ^ k` are the `k`-th power of the ideal `Γ(U, I) ⊆ Γ(U, 𝒪_X)`. -/
theorem ideal_pow (I : QuasicoherentIdealSubsheaf X) (k : ℕ) (U : X.affineOpens) :
    (I ^ k).ideal U = I.ideal U ^ k := by
  have := ClosedImmersionIdeal.isQuasicoherent_unit X
  have := isQuasicoherent_top (E := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  change sub (powSmul (quasicoherentIdealSubsheafEquiv I) k ⊤) U = _
  refine (sub_powSmul_eq _ k isLocal_top U).trans ?_
  exact Ideal.mul_top _

end QuasicoherentIdealSubsheaf

/-- Under the correspondence with Mathlib's affine ideal data, the power `I ^ k` taken in the
ideal sheaf goes to the `k`-th power of the ideal data of `I`. -/
theorem quasicoherentIdealSubsheafEquiv_pow (I : QuasicoherentIdealSubsheaf X) (k : ℕ) :
    quasicoherentIdealSubsheafEquiv (I ^ k) = quasicoherentIdealSubsheafEquiv I ^ k :=
  Scheme.IdealSheafData.ext (funext fun U => I.ideal_pow k U)

namespace QuasicoherentIdealSubsheaf

lemma pow_one (I : QuasicoherentIdealSubsheaf X) : I ^ 1 = I :=
  quasicoherentIdealSubsheafEquiv.injective (by
    rw [quasicoherentIdealSubsheafEquiv_pow, _root_.pow_one])

end QuasicoherentIdealSubsheaf

/-- The closed subschemes cut out by equal ideal data are isomorphic over `X`. -/
private def subschemeIsoOfEq {J K : X.IdealSheafData} (h : J = K) : J.subscheme ≅ K.subscheme where
  hom := Scheme.IdealSheafData.inclusion h.ge
  inv := Scheme.IdealSheafData.inclusion h.le
  hom_inv_id := by simp
  inv_hom_id := by simp

namespace QuasicoherentIdealSubsheaf

/-- **The `n`-th infinitesimal neighbourhood** `Y_n` of the closed subscheme with module ideal
sheaf `I` (Hartshorne II.9, p. 190): the closed subscheme of `X` cut out by `I ^ n`. Hartshorne
defines `Y_n` for `n ≥ 1`; the definition here is made for every `n : ℕ`, and `Y_0` is the empty
subscheme cut out by `I ^ 0 = 𝒪_X`. -/
def infinitesimalNeighborhood (I : QuasicoherentIdealSubsheaf X) (n : ℕ) : Scheme.{u} :=
  (quasicoherentIdealSubsheafEquiv (I ^ n)).subscheme

/-- The closed immersion `Y_n ⟶ X` of the `n`-th infinitesimal neighbourhood. -/
def infinitesimalNeighborhoodι (I : QuasicoherentIdealSubsheaf X) (n : ℕ) :
    I.infinitesimalNeighborhood n ⟶ X :=
  (quasicoherentIdealSubsheafEquiv (I ^ n)).subschemeι

instance (I : QuasicoherentIdealSubsheaf X) (n : ℕ) :
    IsClosedImmersion (I.infinitesimalNeighborhoodι n) :=
  inferInstanceAs (IsClosedImmersion (quasicoherentIdealSubsheafEquiv (I ^ n)).subschemeι)

/-- `Y_n` is cut out by `I ^ n`: the ideal data of its closed immersion is that of `I ^ n`. -/
theorem ker_infinitesimalNeighborhoodι (I : QuasicoherentIdealSubsheaf X) (n : ℕ) :
    (I.infinitesimalNeighborhoodι n).ker = quasicoherentIdealSubsheafEquiv (I ^ n) :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- `Y_n` is cut out by `I ^ n`: the module ideal sheaf of its closed immersion is `I ^ n`. -/
theorem quasicoherentIdealSubsheafEquiv_symm_ker_infinitesimalNeighborhoodι
    (I : QuasicoherentIdealSubsheaf X) (n : ℕ) :
    quasicoherentIdealSubsheafEquiv.symm (I.infinitesimalNeighborhoodι n).ker = I ^ n := by
  rw [ker_infinitesimalNeighborhoodι, Equiv.symm_apply_apply]

end QuasicoherentIdealSubsheaf

/-- **`Y_1 = Y`** (Hartshorne II.9, p. 190). For a closed immersion `f : Y ⟶ X` with module ideal
sheaf `I`, the first infinitesimal neighbourhood (cut out by `I ^ 1 = I`) is `Y` itself, as a
closed subscheme of `X` (`infinitesimalNeighborhoodOneIso_hom_comp`). -/
def infinitesimalNeighborhoodOneIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f] :
    (quasicoherentIdealSubsheafEquiv.symm f.ker).infinitesimalNeighborhood 1 ≅ Y :=
  subschemeIsoOfEq (by
      rw [QuasicoherentIdealSubsheaf.pow_one, Equiv.apply_symm_apply]) ≪≫
    (asIso f.toImage).symm

/-- The identification `Y_1 ≅ Y` is compatible with the closed immersions into `X`. -/
@[reassoc (attr := simp)]
theorem infinitesimalNeighborhoodOneIso_hom_comp {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] :
    (infinitesimalNeighborhoodOneIso f).hom ≫ f =
      (quasicoherentIdealSubsheafEquiv.symm f.ker).infinitesimalNeighborhoodι 1 := by
  have hf : inv f.toImage ≫ f = f.imageι := by
    rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
  change (Scheme.IdealSheafData.inclusion _ ≫ inv f.toImage) ≫ f = _
  rw [Category.assoc, hf]
  exact Scheme.IdealSheafData.inclusion_subschemeι _

/-! ### Deprecated shifted indexing

The declarations below index the neighbourhoods by `I ^ (n + 1)`, so their `n`-th neighbourhood is
the book's `(n + 1)`-st. They are kept, deprecated, for the transition. -/

/-- The closed subscheme of `X` cut out by `I ^ (n + 1)`, the book's `Y_(n+1)`. Deprecated: use
`I.infinitesimalNeighborhood (n + 1)`, indexed as in Hartshorne (II.9, p. 190). -/
@[deprecated QuasicoherentIdealSubsheaf.infinitesimalNeighborhood
  "use `I.infinitesimalNeighborhood (n + 1)` (book indexing)" (since := "2026-11-11")]
def infinitesimalNeighborhood (I : QuasicoherentIdealSubsheaf X) (n : ℕ) : Scheme.{u} :=
  (quasicoherentIdealSubsheafEquiv (I ^ (n + 1))).subscheme

/-- The closed immersion into `X` of the subscheme cut out by `I ^ (n + 1)`. -/
@[deprecated QuasicoherentIdealSubsheaf.infinitesimalNeighborhoodι
  "use `I.infinitesimalNeighborhoodι (n + 1)` (book indexing)" (since := "2026-11-11")]
def infinitesimalNeighborhoodι (I : QuasicoherentIdealSubsheaf X) (n : ℕ) :
    infinitesimalNeighborhood I n ⟶ X :=
  (quasicoherentIdealSubsheafEquiv (I ^ (n + 1))).subschemeι

set_option linter.deprecated false in
/-- The deprecated `infinitesimalNeighborhoodι I n` is a closed immersion. -/
instance (I : QuasicoherentIdealSubsheaf X) (n : ℕ) :
    IsClosedImmersion (infinitesimalNeighborhoodι I n) :=
  inferInstanceAs (IsClosedImmersion (quasicoherentIdealSubsheafEquiv (I ^ (n + 1))).subschemeι)

/-- The ideal data of the closed immersion of the subscheme cut out by `I ^ (n + 1)` is that of
`I ^ (n + 1)`. -/
@[deprecated QuasicoherentIdealSubsheaf.ker_infinitesimalNeighborhoodι
  "use it at `n + 1` (book indexing)" (since := "2026-11-11")]
theorem ker_infinitesimalNeighborhoodι (I : QuasicoherentIdealSubsheaf X) (n : ℕ) :
    (infinitesimalNeighborhoodι I n).ker = quasicoherentIdealSubsheafEquiv (I ^ (n + 1)) :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- The module ideal sheaf of the closed immersion of the subscheme cut out by `I ^ (n + 1)` is
`I ^ (n + 1)`. -/
@[deprecated
  QuasicoherentIdealSubsheaf.quasicoherentIdealSubsheafEquiv_symm_ker_infinitesimalNeighborhoodι
  "use it at `n + 1` (book indexing)" (since := "2026-11-11")]
theorem quasicoherentIdealSubsheafEquiv_symm_ker_infinitesimalNeighborhoodι
    (I : QuasicoherentIdealSubsheaf X) (n : ℕ) :
    quasicoherentIdealSubsheafEquiv.symm (infinitesimalNeighborhoodι I n).ker = I ^ (n + 1) := by
  rw [ker_infinitesimalNeighborhoodι, Equiv.symm_apply_apply]

/-- For a closed immersion `f : Y ⟶ X` with module ideal sheaf `I`, the subscheme cut out by
`I ^ (0 + 1) = I` is `Y` itself, as a closed subscheme of `X`. -/
@[deprecated infinitesimalNeighborhoodOneIso (since := "2026-11-11")]
def infinitesimalNeighborhoodZeroIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f] :
    infinitesimalNeighborhood (quasicoherentIdealSubsheafEquiv.symm f.ker) 0 ≅ Y :=
  subschemeIsoOfEq (by
      rw [zero_add, QuasicoherentIdealSubsheaf.pow_one, Equiv.apply_symm_apply]) ≪≫
    (asIso f.toImage).symm

/-- The identification `infinitesimalNeighborhood I 0 ≅ Y` is compatible with the closed
immersions into `X`. -/
@[deprecated infinitesimalNeighborhoodOneIso_hom_comp (since := "2026-11-11"),
  reassoc (attr := simp)]
theorem infinitesimalNeighborhoodZeroIso_hom_comp {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] :
    (infinitesimalNeighborhoodZeroIso f).hom ≫ f =
      infinitesimalNeighborhoodι (quasicoherentIdealSubsheafEquiv.symm f.ker) 0 := by
  have hf : inv f.toImage ≫ f = f.imageι := by
    rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
  change (Scheme.IdealSheafData.inclusion _ ≫ inv f.toImage) ≫ f = _
  rw [Category.assoc, hf]
  exact Scheme.IdealSheafData.inclusion_subschemeι _

attribute [deprecated infinitesimalNeighborhoodOneIso_hom_comp_assoc (since := "2026-11-11")]
  infinitesimalNeighborhoodZeroIso_hom_comp_assoc

end Hartshorne
