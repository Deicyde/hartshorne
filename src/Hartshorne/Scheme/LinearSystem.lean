/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteLinearSystem
import Hartshorne.Scheme.InvertibleSectionDivisorProjective
import Hartshorne.Scheme.ProjectiveGlobalSectionsFinite

/-!
# Linear systems

Hartshorne, *Algebraic Geometry*, II.7, the definitions of complete linear systems, linear
systems, their dimension, base points and traces (pp. 157–158).

Let `X` be a scheme over a field `k`, with structure morphism `q : X ⟶ Spec k`, and let `L` be an
invertible sheaf on `X`. Then `Γ(X, L)` is a `k`-vector space through the constants
`k → Γ(X, 𝒪_X)`.

## Main definitions and results

* `LinearSystem q L`: a **linear system** of `L`, a finite-dimensional `k`-subspace `V` of
  `Γ(X, L)`. Its **divisors** (`LinearSystem.divisors`) are the divisors of zeros `(s)₀` of the
  nonzero `s ∈ V`. On an integral scheme these are effective
  (`LinearSystem.isEffective_of_mem_divisors`), and when `X` is moreover universally closed over
  an algebraically closed field (e.g. projective) two nonzero sections have the same divisor
  exactly when they differ by a nonzero scalar (`LinearSystem.divisor_eq_iff`, Proposition
  7.7(c)), so the divisors correspond to `(V - 0)/kˣ`.
* `LinearSystem.complete`: the **complete linear system** `V = Γ(X, L)`, finite-dimensional when
  `X` is projective over `k` (Theorem 5.19). If `L ≅ 𝒪_X(D₀)` on an integral `X`, its divisors are
  exactly the effective divisors linearly equivalent to `D₀`, i.e. it is `|D₀|`
  (`LinearSystem.mem_divisors_complete_iff`, Proposition 7.7(a), (b)).
* The partial order of **linear subsystems** (inclusion of subspaces), with
  `LinearSystem.divisors_mono` and `LinearSystem.le_complete`.
* `LinearSystem.dim`: the **dimension** `dim V - 1`.
* `LinearSystem.IsBasePoint`: a **base point**, a point where every section of `V` vanishes. On
  an integral scheme these are the points lying in the support of every divisor of the system
  (`LinearSystem.isBasePoint_iff`); they form the base locus of the existing finite-dimensional
  linear system API (`LinearSystem.mem_support_baseLocusIdeal_iff`), and the linear system spanned
  by a family is `Hartshorne.linearSystem` (`LinearSystem.coe_ofFamily_sections`).
* `LinearSystem.trace`: the **trace** of a linear system along a morphism `i : Y ⟶ X` (for
  Hartshorne a closed immersion of nonsingular projective varieties), the linear system of `i^* L`
  given by the image of `V` under `Γ(X, L) → Γ(Y, i^* L)`.
* `IsDivisorIntersection i hD E`: `E = D·Y`, the effective Cartier divisor on `Y` whose closed
  subscheme is the inverse image `D ∩ Y` of the closed subscheme of the effective divisor `D`.
* `LinearSystem.mem_trace_divisors_iff`: for integral `X` and `Y`, the divisors of the trace are
  exactly the `D·Y` for the divisors `D` of the system whose support does not contain the image of
  `Y`; for `s ∈ V`, the restriction `i^* s` is nonzero exactly when the image of `Y` is not
  contained in the zero locus of `s` (`LinearSystem.pullbackGlobalSection_ne_zero_iff`).

The bridge to the existing zero schemes is
`Scheme.CartierDivisor.IsDivisorOfZeros.idealSheafData_eq_invertibleZeroIdeal`: the ideal of the
divisor of zeros `(s)₀` is the ideal of the zero scheme of `s`.

## Proof

For the bridge, a trivialization `ψ : L|_U ≅ 𝒪_U` gives the trivializing section `e = ψ⁻¹(1)`;
writing `s|_U = g e`, the local equation of `(s)₀` on `U` is `ψ(s|_U) = g`, and the ideal of the
zero scheme on affine opens inside `U` is `(g)` as well. The trace statement then follows from
`Z(i^* s) = i⁻¹ Z(s)` and the fact that on the reduced scheme `Y` a section of an invertible
sheaf vanishing at every point is zero.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.CartierDivisor

namespace Hartshorne

section Bridge

variable {X : Scheme.{u}} {L : X.Modules}

/-- Naturality of the inverse of a trivialization on elements. -/
private theorem trivInv_naturality {U : X.Opens} (ψ : L.over U ≅ SheafOfModules.unit _)
    {V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) :
    L.presheaf.map (homOfLE h).op (ψ.inv.val.app (op (Over.mk (𝟙 U))) r) =
      ψ.inv.val.app (op (Over.mk (homOfLE h))) (X.presheaf.map (homOfLE h).op r) :=
  (ConcreteCategory.congr_hom (ψ.inv.val.naturality
      (Over.homMk (homOfLE h) (Category.comp_id _) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op)
      r).symm

/-- Linearity of the inverse of a trivialization on elements. -/
private theorem trivInv_smul {U : X.Opens} (ψ : L.over U ≅ SheafOfModules.unit _)
    {V : X.Opens} (h : V ≤ U) (a b : Γ(X, V)) :
    a • (show Γ(L, V) from ψ.inv.val.app (op (Over.mk (homOfLE h))) b) =
      ψ.inv.val.app (op (Over.mk (homOfLE h))) (a * b) := by
  have := ((ψ.inv.val.app (op (Over.mk (homOfLE h)))).hom.map_smul a b).symm
  exact this

/-- The generator `ψ⁻¹(1)` of `L|_U` attached to a trivialization `ψ : L|_U ≅ 𝒪_U`. -/
private def trivInv {U : X.Opens} (ψ : L.over U ≅ SheafOfModules.unit _) : Γ(L, U) :=
  ψ.inv.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))

private theorem trivInv_restrict {U : X.Opens} (ψ : L.over U ≅ SheafOfModules.unit _)
    {V : X.Opens} (h : V ≤ U) (a : Γ(X, V)) :
    a • L.presheaf.map (homOfLE h).op (trivInv ψ) =
      ψ.inv.val.app (op (Over.mk (homOfLE h))) a := by
  rw [trivInv, trivInv_naturality, trivInv_smul, map_one, mul_one]

private theorem trivInv_hom_inv {U : X.Opens} (ψ : L.over U ≅ SheafOfModules.unit _)
    {V : X.Opens} (h : V ≤ U) (a : Γ(X, V)) :
    ψ.hom.val.app (op (Over.mk (homOfLE h))) (ψ.inv.val.app (op (Over.mk (homOfLE h))) a) =
      a := by
  have := ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app (op (Over.mk (homOfLE h)))) ψ.inv_hom_id)
    (show (SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj (op (Over.mk (homOfLE h))) from a)
  exact this

private theorem trivInv_inv_hom {U : X.Opens} (ψ : L.over U ≅ SheafOfModules.unit _)
    {V : X.Opens} (h : V ≤ U) (y : Γ(L, V)) :
    ψ.inv.val.app (op (Over.mk (homOfLE h))) (ψ.hom.val.app (op (Over.mk (homOfLE h))) y) =
      y := by
  have := ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app (op (Over.mk (homOfLE h)))) ψ.hom_inv_id)
    (show (L.over U).val.obj (op (Over.mk (homOfLE h))) from y)
  exact this

/-- The generator `ψ⁻¹(1)` of a trivialization is a trivializing section. -/
private theorem isTrivializingSection_trivInv {U : X.Opens}
    (ψ : L.over U ≅ SheafOfModules.unit _) : IsTrivializingSection L U (trivInv ψ) := by
  intro V h
  have key : (fun a : Γ(X, V) => a • L.presheaf.map (homOfLE h).op (trivInv ψ)) =
      fun a => ψ.inv.val.app (op (Over.mk (homOfLE h))) a := by
    funext a
    exact trivInv_restrict ψ h a
  rw [key]
  exact Function.bijective_iff_has_inverse.mpr ⟨fun y => ψ.hom.val.app (op (Over.mk (homOfLE h)))
    (show (L.over U).val.obj (op (Over.mk (homOfLE h))) from y),
    fun a => trivInv_hom_inv ψ h a, fun y => trivInv_inv_hom ψ h y⟩

/-- If `s|_U = g ψ⁻¹(1)` then `ψ(s|_U) = g`. -/
private theorem trivApply_eq_of_eq_smul {U : X.Opens} (ψ : L.over U ≅ SheafOfModules.unit _)
    {s : Γ(L, ⊤)} {g : Γ(X, U)}
    (hs : L.presheaf.map (homOfLE le_top).op s = g • trivInv ψ) :
    trivApply ψ (resTop L U s) = g := by
  have h1 : g • trivInv ψ = ψ.inv.val.app (op (Over.mk (𝟙 U))) g := by
    have := trivInv_restrict ψ (le_refl U) g
    rwa [show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, L.presheaf.map_id] at this
  have h3 := congrArg (fun y : Γ(L, U) => ψ.hom.val.app (op (Over.mk (𝟙 U)))
      (show (L.over U).val.obj (op (Over.mk (𝟙 U))) from y)) (hs.trans h1)
  exact h3.trans (trivInv_hom_inv ψ (le_refl U) g)

end Bridge

end Hartshorne

namespace AlgebraicGeometry.Scheme.CartierDivisor

open Hartshorne

variable {X : Scheme.{u}} {L : X.Modules}

/-- **The divisor of zeros is the zero scheme.** If `D = (s)₀` is the divisor of zeros of a
global section `s` of an invertible sheaf `L` (Hartshorne II.7, p.157) and `D` is effective, then
the ideal sheaf of `D` is the ideal sheaf of the zero scheme of `s`. -/
theorem IsDivisorOfZeros.idealSheafData_eq_invertibleZeroIdeal {s : Γ(L, ⊤)}
    {D : X.CartierDivisor} (hD : IsDivisorOfZeros L s D) (hL : L.IsInvertible)
    (hDeff : D.IsEffective) : idealSheafData hDeff = invertibleZeroIdeal hL s := by
  have hx : ∀ x : X, ∃ (U : X.Opens) (_ : L.over U ≅ SheafOfModules.unit _) (W : X.affineOpens),
      x ∈ (W : X.Opens) ∧ (W : X.Opens) ≤ U := by
    intro x
    obtain ⟨U, hxU, ⟨α⟩⟩ := hL x
    obtain ⟨γ⟩ := (Scheme.Modules.nonempty_restrict_iso_free_iff L U _).mp ⟨α⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    exact ⟨U, γ ≪≫ coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit _),
      ⟨W, hW⟩, hxW, hWU⟩
  choose U ψ W hxW hWU using hx
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W
    (eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩) fun x => ?_
  have he := isTrivializingSection_trivInv (ψ x)
  obtain ⟨g, hg⟩ := he.exists_eq_smul s
  obtain ⟨f, hf, hDU⟩ := hD (U x) (ψ x)
  rw [trivApply_eq_of_eq_smul (ψ x) hg] at hf
  rw [idealSheafData_ideal_eq_span hDeff hDU hf (W x) (hWU x)]
  have hg' : L.presheaf.map (homOfLE le_top).op s = X.presheaf.map (homOfLE (hWU x)).op g •
      L.presheaf.map (homOfLE (hWU x)).op (trivInv (ψ x)) := by
    rw [← Scheme.Modules.map_map_homOfLE _ (le_top : U x ≤ ⊤) (hWU x), hg,
      Scheme.Modules.map_smul]
  rw [invertibleZeroIdeal_ideal_eq_span hL (he.restrict (hWU x)) hg']

/-- The support of the divisor of zeros `(s)₀` is the zero locus of `s`. -/
theorem IsDivisorOfZeros.mem_support_iff {s : Γ(L, ⊤)} {D : X.CartierDivisor}
    (hD : IsDivisorOfZeros L s D) (hL : L.IsInvertible) (hDeff : D.IsEffective) (x : X) :
    x ∈ (idealSheafData hDeff).support ↔ x ∉ nonvanishingLocus L s := by
  rw [hD.idealSheafData_eq_invertibleZeroIdeal hL hDeff, mem_support_invertibleZeroIdeal_iff]

/-- On an integral scheme, a nonzero section of an invertible sheaf has an effective divisor of
zeros. -/
theorem exists_isDivisorOfZeros_isEffective [IsIntegral X] (hL : L.IsInvertible) {s : Γ(L, ⊤)}
    (hs : s ≠ 0) : ∃ D : X.CartierDivisor, IsDivisorOfZeros L s D ∧ D.IsEffective := by
  obtain ⟨D₀, ⟨χ⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso hL
  obtain ⟨D, hD, hDeff, -⟩ := exists_isDivisorOfZeros χ.symm hs
  exact ⟨D, hD, hDeff⟩

end AlgebraicGeometry.Scheme.CartierDivisor

namespace Hartshorne

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The global sections `Γ(X, L)` as a `k`-vector space, for a scheme `X` over `k` with structure
morphism `q`: scalars act through the constants `k → Γ(X, 𝒪_X)`. -/
abbrev globalSectionsOverField (q : X ⟶ Spec (.of k)) (L : X.Modules) : ModuleCat k :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom).obj (L.val.obj (op ⊤))

/-- **A linear system** (Hartshorne II.7, p.157) of an invertible sheaf `L` on a scheme `X` over
`k`: a finite-dimensional `k`-subspace `V ⊆ Γ(X, L)`. Its divisors are the divisors of zeros of the
nonzero sections in `V` (`LinearSystem.divisors`); sections differing by a nonzero scalar give the
same divisor. -/
@[ext]
structure LinearSystem (q : X ⟶ Spec (.of k)) (L : X.Modules) where
  /-- `L` is invertible. -/
  isInvertible : L.IsInvertible
  /-- The subspace `V ⊆ Γ(X, L)`. -/
  sections : Submodule k (globalSectionsOverField q L)
  /-- `V` is finite-dimensional. -/
  finiteDimensional : FiniteDimensional k sections

namespace LinearSystem

variable {q : X ⟶ Spec (.of k)} {L : X.Modules}

attribute [instance] LinearSystem.finiteDimensional

/-- A section `s ∈ V`, as a global section of `L`. -/
abbrev toSection (s : globalSectionsOverField q L) : Γ(L, ⊤) := s

/-- **The divisors of a linear system**: the divisors of zeros `(s)₀` of the nonzero sections
`s ∈ V`. -/
def divisors (𝔡 : LinearSystem q L) : Set X.CartierDivisor :=
  {D | ∃ s ∈ 𝔡.sections, s ≠ 0 ∧ IsDivisorOfZeros L (toSection s) D}

/-- On an integral scheme, the divisors of a linear system are effective. -/
theorem isEffective_of_mem_divisors [IsIntegral X] (𝔡 : LinearSystem q L) {D : X.CartierDivisor}
    (hD : D ∈ 𝔡.divisors) : D.IsEffective := by
  obtain ⟨s, -, -, hsD⟩ := hD
  obtain ⟨D₀, ⟨χ⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso 𝔡.isInvertible
  exact hsD.isEffective χ.symm

/-- On an integral scheme, every nonzero section of a linear system has a divisor in it. -/
theorem exists_mem_divisors [IsIntegral X] (𝔡 : LinearSystem q L)
    {s : globalSectionsOverField q L} (hsV : s ∈ 𝔡.sections) (hs : s ≠ 0) :
    ∃ D ∈ 𝔡.divisors, IsDivisorOfZeros L (toSection s) D := by
  obtain ⟨D, hD, -⟩ := exists_isDivisorOfZeros_isEffective 𝔡.isInvertible hs
  exact ⟨D, ⟨s, hsV, hs, hD⟩, hD⟩

/-- **Sections modulo scalars** (Hartshorne II.7, Proposition 7.7(c)). On an integral scheme
universally closed over an algebraically closed field `k` (e.g. a projective variety), two
nonzero sections of `L` have the same divisor of zeros exactly when they differ by a nonzero
scalar. So the divisors of a linear system `V` correspond to `(V - 0)/kˣ`. -/
theorem divisor_eq_iff [IsAlgClosed k] [IsIntegral X] [UniversallyClosed q] (hL : L.IsInvertible)
    {s s' : globalSectionsOverField q L} (hs : s ≠ 0) (hs' : s' ≠ 0) {D D' : X.CartierDivisor}
    (hD : IsDivisorOfZeros L (toSection s) D) (hD' : IsDivisorOfZeros L (toSection s') D') :
    D = D' ↔ ∃ c : kˣ, s' = (c : k) • s := by
  obtain ⟨D₀, ⟨χ⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso hL
  exact isDivisorOfZeros_eq_iff q χ.symm hs hs' hD hD'

/-- **The complete linear system** (Hartshorne II.7, p.157): all of `Γ(X, L)`, which is
finite-dimensional when `X` is projective over `k` (Hartshorne II, Theorem 5.19). -/
def complete (hq : Projective q) (hL : L.IsInvertible) : LinearSystem q L where
  isInvertible := hL
  sections := ⊤
  finiteDimensional := by
    have := ((Scheme.Modules.isInvertible_iff_ringed L).mp hL).isFiniteLocallyFree
    have : SheafOfModules.IsFinitePresentation.{u, u, u} L := this.isFinitePresentation
    have := finiteDimensional_globalSections_of_projective q hq L
      (isCoherent_of_isFinitePresentation L)
    infer_instance

@[simp]
theorem complete_sections (hq : Projective q) (hL : L.IsInvertible) :
    (complete hq hL).sections = ⊤ := rfl

/-- **The complete linear system is `|D₀|`** (Hartshorne II.7, p.157, via Proposition 7.7(a),
(b)). If `L ≅ 𝒪_X(D₀)` on an integral scheme projective over `k`, the divisors of the complete
linear system of `L` are exactly the effective divisors linearly equivalent to `D₀`. -/
theorem mem_divisors_complete_iff [IsIntegral X] (hq : Projective q) (hL : L.IsInvertible)
    {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf) (D : X.CartierDivisor) :
    D ∈ (complete hq hL).divisors ↔ D.IsEffective ∧ D.LinearEquivalent D₀ := by
  constructor
  · rintro ⟨s, -, hs, hsD⟩
    obtain ⟨D', hD', hD'eff, hlin⟩ := exists_isDivisorOfZeros φ hs
    rw [hsD.unique φ hD']
    exact ⟨hD'eff, hlin⟩
  · rintro ⟨hDeff, hlin⟩
    obtain ⟨s, hs, hsD⟩ := exists_section_isDivisorOfZeros φ hDeff hlin
    exact ⟨s, Submodule.mem_top, hs, hsD⟩

open AlgebraicGeometry.Scheme in
/-- **The complete linear system is `|D₀|`, Weil-divisor form** (Hartshorne II.7, p.157, via
Proposition 7.7(a), (b)). Let `X` be a nonsingular projective variety over `k` and
`L ≅ 𝒪_X(D₀)` for a Weil divisor `D₀`. A Weil divisor `D` is a divisor of the complete linear
system of `L` exactly when it is effective and linearly equivalent to `D₀`. -/
theorem mem_divisors_complete_iff_weil [IsIntegral X] (hq : Projective q) (hreg : X.IsRegular)
    (hL : L.IsInvertible) :
    letI := isNoetherian_of_projective q hq
    letI := isSeparated_of_projective q hq
    ∀ {D₀ : X.WeilDivisor}, (L ≅ (weilCartierEquiv hreg.isLocallyFactorial D₀).sheaf) →
      ∀ D : X.WeilDivisor,
        (weilCartierEquiv hreg.isLocallyFactorial D ∈ (complete hq hL).divisors ↔
          WeilDivisor.IsEffective D ∧ WeilDivisor.LinearEquivalent
            (satisfiesConditionStar_of_isLocallyFactorial hreg.isLocallyFactorial) D D₀) := by
  let := isNoetherian_of_projective q hq
  let := isSeparated_of_projective q hq
  intro D₀ φ D
  constructor
  · rintro ⟨s, -, hs, hsD⟩
    obtain ⟨D', hD', hD'eff, hlin⟩ := exists_isDivisorOfZeros_of_projective q hq hreg φ hs
    rw [(weilCartierEquiv hreg.isLocallyFactorial).injective (hsD.unique φ hD')]
    exact ⟨hD'eff, hlin⟩
  · rintro ⟨hDeff, hlin⟩
    obtain ⟨s, hs, hsD⟩ := exists_section_isDivisorOfZeros_of_projective q hq hreg φ hDeff hlin
    exact ⟨s, Submodule.mem_top, hs, hsD⟩

/-- Linear subsystems: `𝔡 ≤ 𝔡'` when the subspace of `𝔡` is contained in that of `𝔡'`
(Hartshorne II.7, p.157). -/
instance : PartialOrder (LinearSystem q L) :=
  PartialOrder.lift LinearSystem.sections fun _ _ h => LinearSystem.ext h

theorem le_iff {𝔡 𝔡' : LinearSystem q L} : 𝔡 ≤ 𝔡' ↔ 𝔡.sections ≤ 𝔡'.sections := Iff.rfl

/-- A linear subsystem has fewer divisors. -/
theorem divisors_mono {𝔡 𝔡' : LinearSystem q L} (h : 𝔡 ≤ 𝔡') : 𝔡.divisors ⊆ 𝔡'.divisors := by
  rintro D ⟨s, hsV, hs, hsD⟩
  exact ⟨s, h hsV, hs, hsD⟩

/-- Every linear system is a linear subsystem of the complete linear system. -/
theorem le_complete (hq : Projective q) (𝔡 : LinearSystem q L) :
    𝔡 ≤ complete hq 𝔡.isInvertible :=
  fun _ _ => Submodule.mem_top

/-- **The dimension of a linear system** (Hartshorne II.7, p.157): the dimension of `V` minus
one, its dimension as a projective space. -/
def dim (𝔡 : LinearSystem q L) : ℤ := Module.finrank k 𝔡.sections - 1

/-- The dimension of the complete linear system is `dim_k Γ(X, L) - 1`. -/
theorem dim_complete (hq : Projective q) (hL : L.IsInvertible) :
    (complete hq hL).dim = Module.finrank k (globalSectionsOverField q L) - 1 := by
  rw [dim, complete_sections, finrank_top]

/-- The dimension is monotone along linear subsystems. -/
theorem dim_mono {𝔡 𝔡' : LinearSystem q L} (h : 𝔡 ≤ 𝔡') : 𝔡.dim ≤ 𝔡'.dim := by
  have := Submodule.finrank_mono (R := k) (M := 𝔡'.sections)
    (show Submodule.comap 𝔡'.sections.subtype 𝔡.sections ≤ ⊤ from le_top)
  rw [dim, dim, sub_le_sub_iff_right, Nat.cast_le]
  rw [finrank_top, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
    inf_eq_right.mpr h] at this
  exact this

/-- **A base point** of a linear system (Hartshorne II.7, p.158): a point at which every section
of `V` vanishes. -/
def IsBasePoint (𝔡 : LinearSystem q L) (x : X) : Prop :=
  ∀ s ∈ 𝔡.sections, x ∉ nonvanishingLocus L (toSection s)

/-- The base points are the points of the (scheme-theoretic) base locus of `V`. -/
theorem mem_support_baseLocusIdeal_iff (𝔡 : LinearSystem q L) (x : X) :
    x ∈ (baseLocusIdeal 𝔡.isInvertible
      (toSection '' (𝔡.sections : Set (globalSectionsOverField q L)))).support ↔
      𝔡.IsBasePoint x := by
  rw [Hartshorne.mem_support_baseLocusIdeal_iff, Set.forall_mem_image]
  rfl

/-- **Base points via divisors** (Hartshorne II.7, p.158). On an integral scheme, `x` is a base
point of `𝔡` exactly when it lies in the support of every divisor of `𝔡`. -/
theorem isBasePoint_iff [IsIntegral X] (𝔡 : LinearSystem q L) (x : X) :
    𝔡.IsBasePoint x ↔
      ∀ D ∈ 𝔡.divisors, ∀ hD : D.IsEffective, x ∈ (idealSheafData hD).support := by
  constructor
  · rintro h D ⟨s, hsV, -, hsD⟩ hD
    exact (hsD.mem_support_iff 𝔡.isInvertible hD x).mpr (h s hsV)
  · intro h s hsV
    by_cases hs : s = 0
    · rw [hs]
      show x ∉ nonvanishingLocus L 0
      rw [nonvanishingLocus_zero]
      exact Set.notMem_empty x
    · obtain ⟨D, hDmem, hD⟩ := 𝔡.exists_mem_divisors hsV hs
      have hDeff := 𝔡.isEffective_of_mem_divisors hDmem
      exact (hD.mem_support_iff 𝔡.isInvertible hDeff x).mp (h D hDmem hDeff)

/-- **The linear system spanned by a family** `s₀, …, sₙ` of sections of `L`. Its subspace is the
set `Hartshorne.linearSystem q s` of combinations `∑ aᵢ sᵢ` (`coe_ofFamily_sections`). -/
def ofFamily (hL : L.IsInvertible) {n : ℕ} (s : Fin (n + 1) → globalSectionsOverField q L) :
    LinearSystem q L where
  isInvertible := hL
  sections := Submodule.span k (Set.range s)
  finiteDimensional := FiniteDimensional.span_of_finite k (Set.finite_range s)

/-- The subspace spanned by `s₀, …, sₙ` is the set of combinations `∑ aᵢ sᵢ`. -/
theorem mem_ofFamily_sections_iff (hL : L.IsInvertible) {n : ℕ}
    (s : Fin (n + 1) → globalSectionsOverField q L) (t : globalSectionsOverField q L) :
    t ∈ (ofFamily hL s).sections ↔ toSection t ∈ linearSystem q (fun i => toSection (s i)) := by
  change t ∈ Submodule.span k (Set.range s) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  rfl

section Trace

variable {Y : Scheme.{u}}

/-- The `k`-linear restriction map `Γ(X, L) → Γ(Y, i^* L)`, `s ↦ i^* s`. -/
def restrictionMap (i : Y ⟶ X) (q : X ⟶ Spec (.of k)) (L : X.Modules) :
    globalSectionsOverField q L →ₗ[k]
      globalSectionsOverField (i ≫ q) ((Scheme.Modules.pullback i).obj L) where
  toFun s := pullbackGlobalSection i (toSection s)
  map_add' a b := pullbackGlobalSection_add i a b
  map_smul' c s := by
    change pullbackGlobalSection i (kConst q c • toSection s) =
      kConst (i ≫ q) c • pullbackGlobalSection i (toSection s)
    rw [pullbackGlobalSection_smul, appTop_kConst]

theorem restrictionMap_apply (i : Y ⟶ X) (s : globalSectionsOverField q L) :
    toSection (restrictionMap i q L s) = pullbackGlobalSection i (toSection s) := rfl

/-- **The trace of a linear system** (Hartshorne II.7, p.158). For a morphism `i : Y ⟶ X`
(Hartshorne takes a closed immersion of nonsingular projective varieties), the trace of `𝔡` on
`Y` is the linear system of `i^* L` given by the image of `V` under `Γ(X, L) → Γ(Y, i^* L)`. -/
def trace (𝔡 : LinearSystem q L) (i : Y ⟶ X) :
    LinearSystem (i ≫ q) ((Scheme.Modules.pullback i).obj L) where
  isInvertible := 𝔡.isInvertible.pullback i
  sections := 𝔡.sections.map (restrictionMap i q L)
  finiteDimensional := inferInstance

theorem mem_trace_sections_iff (𝔡 : LinearSystem q L) (i : Y ⟶ X)
    (t : globalSectionsOverField (i ≫ q) ((Scheme.Modules.pullback i).obj L)) :
    t ∈ (𝔡.trace i).sections ↔
      ∃ s ∈ 𝔡.sections, pullbackGlobalSection i (toSection s) = toSection t :=
  Submodule.mem_map

/-- On a reduced scheme `Y`, the restriction `i^* s` of a section of an invertible sheaf is
nonzero exactly when `s` does not vanish at some point of the image of `Y`. -/
theorem pullbackGlobalSection_ne_zero_iff [IsReduced Y] (i : Y ⟶ X) (hL : L.IsInvertible)
    (s : Γ(L, ⊤)) : pullbackGlobalSection i s ≠ 0 ↔ ∃ y, i y ∈ nonvanishingLocus L s := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    exact h (eq_zero_of_forall_notMem_nonvanishingLocus (hL.pullback i) fun y hy =>
      hno y ((mem_nonvanishingLocus_pullbackGlobalSection_iff i hL s y).mp hy))
  · rintro ⟨y, hy⟩ h
    have := (mem_nonvanishingLocus_pullbackGlobalSection_iff i hL s y).mpr hy
    rw [h, nonvanishingLocus_zero] at this
    exact this

end Trace

end LinearSystem

/-- **The intersection divisor `D·Y`.** For a morphism `i : Y ⟶ X` and an effective Cartier
divisor `D` on `X`, `E` is `D·Y` if it is an effective Cartier divisor on `Y` whose closed
subscheme is the inverse image `D ∩ Y` of the closed subscheme of `D`. -/
def IsDivisorIntersection {Y : Scheme.{u}} (i : Y ⟶ X) {D : X.CartierDivisor} (hD : D.IsEffective)
    (E : Y.CartierDivisor) : Prop :=
  ∃ hE : E.IsEffective, idealSheafData hE = (idealSheafData hD).comap i

/-- `D·Y` is unique. -/
theorem IsDivisorIntersection.unique {Y : Scheme.{u}} {i : Y ⟶ X} {D : X.CartierDivisor}
    {hD : D.IsEffective} {E E' : Y.CartierDivisor} (hE : IsDivisorIntersection i hD E)
    (hE' : IsDivisorIntersection i hD E') : E = E' := by
  obtain ⟨hE, h⟩ := hE
  obtain ⟨hE', h'⟩ := hE'
  exact idealSheafData_injective hE hE' (h.trans h'.symm)

namespace LinearSystem

variable {q : X ⟶ Spec (.of k)} {L : X.Modules} {Y : Scheme.{u}}

/-- **The divisors of the trace** (Hartshorne II.7, p.158). For integral schemes `X` and `Y` and
a morphism `i : Y ⟶ X`, the divisors of the trace of `𝔡` on `Y` are exactly the intersection
divisors `D·Y` for the divisors `D` of `𝔡` whose support does not contain the image of `Y`; no
intersection divisor is assigned to a `D` whose support contains the image of `Y`, since then
the restricted section is zero. -/
theorem mem_trace_divisors_iff [IsIntegral X] [IsIntegral Y] (𝔡 : LinearSystem q L) (i : Y ⟶ X)
    (E : Y.CartierDivisor) :
    E ∈ (𝔡.trace i).divisors ↔
      ∃ D ∈ 𝔡.divisors, ∃ hD : D.IsEffective,
        ¬ Set.range i ⊆ ((idealSheafData hD).support : Set X) ∧ IsDivisorIntersection i hD E := by
  have hL := 𝔡.isInvertible
  constructor
  · rintro ⟨t, htV, ht, htE⟩
    obtain ⟨s, hsV, rfl⟩ := Submodule.mem_map.mp htV
    have hs : s ≠ 0 := by
      rintro rfl
      exact ht (map_zero _)
    obtain ⟨D, hDmem, hD⟩ := 𝔡.exists_mem_divisors hsV hs
    have hDeff := 𝔡.isEffective_of_mem_divisors hDmem
    have hEeff := (𝔡.trace i).isEffective_of_mem_divisors ⟨_, htV, ht, htE⟩
    refine ⟨D, hDmem, hDeff, ?_, hEeff, ?_⟩
    · intro hsub
      obtain ⟨y, hy⟩ := (pullbackGlobalSection_ne_zero_iff i hL (toSection s)).mp ht
      exact (hD.mem_support_iff hL hDeff (i y)).mp (hsub ⟨y, rfl⟩) hy
    · rw [htE.idealSheafData_eq_invertibleZeroIdeal (hL.pullback i) hEeff,
        hD.idealSheafData_eq_invertibleZeroIdeal hL hDeff]
      exact invertibleZeroIdeal_pullbackGlobalSection hL i (toSection s)
  · rintro ⟨D, ⟨s, hsV, -, hD⟩, hDeff, hnot, hEeff, hE⟩
    have ht : restrictionMap i q L s ≠ 0 := by
      refine (pullbackGlobalSection_ne_zero_iff i hL (toSection s)).mpr ?_
      by_contra hno
      push Not at hno
      exact hnot (by
        rintro _ ⟨y, rfl⟩
        exact (hD.mem_support_iff hL hDeff (i y)).mpr (hno y))
    obtain ⟨E', hE'mem, hE'⟩ :=
      (𝔡.trace i).exists_mem_divisors (Submodule.mem_map_of_mem hsV) ht
    have hE'eff := (𝔡.trace i).isEffective_of_mem_divisors hE'mem
    have hEE' : E = E' := by
      refine idealSheafData_injective hEeff hE'eff ?_
      rw [hE, hE'.idealSheafData_eq_invertibleZeroIdeal (hL.pullback i) hE'eff,
        hD.idealSheafData_eq_invertibleZeroIdeal hL hDeff]
      exact (invertibleZeroIdeal_pullbackGlobalSection hL i (toSection s)).symm
    rw [hEE']
    exact hE'mem

end LinearSystem

end Hartshorne
