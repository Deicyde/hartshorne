/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.DualizingSheaf

/-!
# Uniqueness of the dualizing sheaf

Hartshorne, *Algebraic Geometry*, III, Proposition 7.2 (p. 241).

Let `X` be a proper scheme of dimension `n` over a field `k`. If `(ω, t)` and `(ω', t')` are
dualizing sheaves for `X`, there is a unique isomorphism `φ : ω ≅ ω'` with `t = t' ∘ Hⁿ(φ)`
(`Hartshorne.DualizingSheaf.existsUnique_iso`).

The proof is the book's: a dualizing sheaf `(ω, t)` represents the contravariant functor
`F ↦ Hⁿ(X, F)^∨` on coherent `𝒪_X`-modules (`Hartshorne.DualizingSheaf.representableBy`), the
element of `Hⁿ(X, ω)^∨` corresponding to the identity of `ω` being `t`. Representing objects are
unique up to a unique isomorphism compatible with these elements
(`CategoryTheory.Functor.RepresentableBy.uniqueUpToIso`), which gives the isomorphism
`Hartshorne.DualizingSheaf.uniqueIso`, and uniqueness follows from the injectivity of
`Hom_X(ω, ω') ⟶ Hⁿ(X, ω)^∨`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The contravariant functor `F ↦ Hⁿ(X, F)^∨` on coherent `𝒪_X`-modules, valued in types. A
morphism `g : F' ⟶ F` acts on a functional `λ` on `Hⁿ(X, F)` by `λ ↦ λ ∘ Hⁿ(g)`. -/
def topCohomologyDual (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    (ObjectProperty.FullSubcategory (IsCoherent (X := X)))ᵒᵖ ⥤ Type u where
  obj F := Module.Dual k ((cohomologyOverField f n).obj F.unop.obj)
  map g := ↾fun l ↦ l ∘ₗ ((cohomologyOverField f n).map g.unop.hom).hom
  map_id F := by
    ext l x
    simp
  map_comp g g' := by
    ext l x
    simp

namespace DualizingSheaf

variable {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f] {n : ℕ} {hdim : topologicalKrullDim X = n}

/-- The coherent module `ω°_X` of a dualizing sheaf, as an object of the category of coherent
`𝒪_X`-modules. -/
def coherentSheaf (D : DualizingSheaf f n hdim) :
    ObjectProperty.FullSubcategory (IsCoherent (X := X)) :=
  ⟨D.sheaf, D.isCoherent⟩

/-- A dualizing sheaf `(ω°_X, t)` represents the functor `F ↦ Hⁿ(X, F)^∨` on coherent
`𝒪_X`-modules, through the isomorphisms `Hom_X(F, ω°_X) ≃ Hⁿ(X, F)^∨`, `φ ↦ t ∘ Hⁿ(φ)`
(Hartshorne III, proof of Proposition 7.2, p. 241). -/
def representableBy (D : DualizingSheaf f n hdim) :
    (topCohomologyDual f n).RepresentableBy D.coherentSheaf where
  homEquiv {F} := InducedCategory.homEquiv.trans (D.dualityEquiv F.obj F.property).toEquiv
  homEquiv_comp {F F'} g φ := D.dualityEquiv_naturality F'.property F.property g.hom φ.hom

/-- The bijection `Hom_X(F, ω°_X) ≃ Hⁿ(X, F)^∨` of `representableBy` is `φ ↦ t ∘ Hⁿ(φ)`. -/
theorem representableBy_homEquiv_apply (D : DualizingSheaf f n hdim)
    {F : ObjectProperty.FullSubcategory (IsCoherent (X := X))} (φ : F ⟶ D.coherentSheaf) :
    D.representableBy.homEquiv φ = dualityPairingMap f n D.trace F.obj φ.hom :=
  rfl

/-- The element of `Hⁿ(X, ω°_X)^∨` corresponding to the identity of `ω°_X` is the trace. -/
theorem representableBy_homEquiv_id (D : DualizingSheaf f n hdim) :
    D.representableBy.homEquiv (𝟙 D.coherentSheaf) = D.trace := by
  refine LinearMap.ext fun x ↦ ?_
  change D.trace (((cohomologyOverField f n).map (𝟙 D.sheaf)).hom x) = D.trace x
  rw [CategoryTheory.Functor.map_id, ModuleCat.hom_id]
  rfl

/-- The isomorphism `ω ≅ ω'` between two dualizing sheaves `(ω, t)` and `(ω', t')` of `X`
compatible with the traces (Hartshorne III, Proposition 7.2, p. 241): the isomorphism between
two objects representing `F ↦ Hⁿ(X, F)^∨`. -/
def uniqueIso (D D' : DualizingSheaf f n hdim) : D.sheaf ≅ D'.sheaf :=
  (ObjectProperty.ι _).mapIso (D.representableBy.uniqueUpToIso D'.representableBy)

/-- The isomorphism `φ : ω ≅ ω'` between two dualizing sheaves satisfies `t = t' ∘ Hⁿ(φ)`. -/
theorem trace_eq_comp_uniqueIso (D D' : DualizingSheaf f n hdim) :
    D.trace = D'.trace ∘ₗ ((cohomologyOverField f n).map (uniqueIso D D').hom).hom := by
  have h : (uniqueIso D D').hom =
      (D'.representableBy.homEquiv.symm (D.representableBy.homEquiv (𝟙 D.coherentSheaf))).hom :=
    rfl
  rw [h, representableBy_homEquiv_id]
  exact ((D'.representableBy.homEquiv (X := D.coherentSheaf)).apply_symm_apply D.trace).symm

/-- **Uniqueness of the dualizing sheaf** (Hartshorne III, Proposition 7.2, p. 241). Let `X` be a
proper scheme of dimension `n` over a field `k`. If `(ω, t)` and `(ω', t')` are dualizing sheaves
for `X`, there is a unique isomorphism `φ : ω ≅ ω'` such that `t = t' ∘ Hⁿ(φ)`. -/
theorem existsUnique_iso (D D' : DualizingSheaf f n hdim) :
    ∃! φ : D.sheaf ≅ D'.sheaf,
      D.trace = D'.trace ∘ₗ ((cohomologyOverField f n).map φ.hom).hom := by
  refine ⟨uniqueIso D D', trace_eq_comp_uniqueIso D D', fun ψ hψ ↦ ?_⟩
  ext1
  apply (D'.bijective_dualityPairingMap D.sheaf D.isCoherent).1
  change D'.trace ∘ₗ ((cohomologyOverField f n).map ψ.hom).hom =
    D'.trace ∘ₗ ((cohomologyOverField f n).map (uniqueIso D D').hom).hom
  rw [← hψ, ← trace_eq_comp_uniqueIso]

end DualizingSheaf

end Hartshorne
