/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.LocalIntersectionMultiplicity
import Hartshorne.Scheme.DimensionAtClosedPoint
import Hartshorne.Scheme.Differentials.RegularQuotientCotangentIndependent
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Transverse intersection of curves on a surface

Hartshorne, *Algebraic Geometry*, V.1 (p. 357): curves `C, D` on a surface `X` **meet
transversally** at a point `P` if local equations `f, g ∈ 𝒪_{X,P}` of `C, D` at `P` generate the
maximal ideal `𝔪_P` of `𝒪_{X,P}`.

* `Hartshorne.Surface.IsTransverseAt C D P`: some local equations `f, g` of `C, D` at `P`
  generate `𝔪_P`.
* `Hartshorne.Surface.isTransverseAt_iff`: the condition does not depend on the chosen local
  equations: for *any* local equations `f, g`, `C, D` meet transversally at `P` if and only if
  `(f, g) = 𝔪_P`.

Let `C, D` meet transversally at a closed point `P`, with local equations `f, g`. The following
consequences of the definition are recorded.

* `Hartshorne.Surface.IsTransverseAt.isRegularLocalRing_left` (and `_right`): `C` (and `D`) is
  regular at `P`, i.e. its local ring `𝒪_{C,P} = 𝒪_{X,P}/(f)` is a regular local ring.
* `Hartshorne.Surface.IsTransverseAt.length_eq_one`, `IsTransverseAt.isReduced`,
  `IsTransverseAt.bijective_quotient_mk_comp_stalkStructureMap`: the local ring
  `𝒪_{X,P}/(f, g)` of the scheme-theoretic intersection `C ∩ D` at `P` has length one, is
  reduced, and is `k` itself (the composite `k → 𝒪_{X,P} → 𝒪_{X,P}/(f, g)` is bijective).
  Equivalently `(C.D)_P = 1` (`IsTransverseAt.localIntersectionMultiplicity_eq_one`).
* `Hartshorne.Surface.IsTransverseAt.linearIndependent_toCotangent`: the embedded tangent lines
  of `C` and `D` at `P` are distinct. The Zariski tangent space of `X` at `P` is the dual of the
  cotangent space `𝔪_P/𝔪_P²`, and the embedded tangent line of `C` at `P` is the subspace cut out
  by `df`, the class of `f` in `𝔪_P/𝔪_P²` (the kernel of `𝔪_P/𝔪_P² → 𝔪_{C,P}/𝔪_{C,P}²` is
  spanned by that class). Two such lines are distinct exactly when the classes of `f` and `g`
  in `𝔪_P/𝔪_P²` are linearly independent over the residue field, which is the statement proved.

## Proof

At a closed point `P` the local ring `𝒪_{X,P}` is regular of dimension two (Exercise II.3.20),
so `𝔪_P/𝔪_P²` has dimension two. When `f, g` generate `𝔪_P`, their classes span `𝔪_P/𝔪_P²`,
hence form a basis: `f, g` is a regular system of parameters. A quotient of a regular local ring
by part of a regular system of parameters is regular, so `𝒪_{X,P}/(f)` and `𝒪_{X,P}/(g)` are
regular. Finally `𝒪_{X,P}/(f, g) = 𝒪_{X,P}/𝔪_P` is the residue field, which is `k` at a closed
point since `k` is algebraically closed.
-/

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hartshorne

namespace Surface

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Surface k)

/-- **Transverse intersection** (Hartshorne V.1, p. 357). The curves `C` and `D` on the surface
meet transversally at `P` when local equations `f, g ∈ 𝒪_{X,P}` of `C, D` at `P` generate the
maximal ideal `𝔪_P`. By `isTransverseAt_iff` this does not depend on the choice of local
equations. (The definition is used at closed points `P ∈ C ∩ D`; the generation condition forces
`f, g ∈ 𝔪_P`, i.e. `P ∈ C ∩ D`.) -/
def IsTransverseAt (C D : S.Curve) (P : S.X) : Prop :=
  ∃ f g : S.X.presheaf.stalk P, S.IsLocalEquation C.1 P f ∧ S.IsLocalEquation D.1 P g ∧
    Ideal.span {f, g} = maximalIdeal (S.X.presheaf.stalk P)

variable {S}

/-- **Independence of the local equations.** For any local equations `f, g` of `C, D` at `P`,
`C` and `D` meet transversally at `P` if and only if `f, g` generate `𝔪_P`. -/
theorem isTransverseAt_iff {C D : S.Curve} {P : S.X} {f g : S.X.presheaf.stalk P}
    (hf : S.IsLocalEquation C.1 P f) (hg : S.IsLocalEquation D.1 P g) :
    S.IsTransverseAt C D P ↔ Ideal.span {f, g} = maximalIdeal (S.X.presheaf.stalk P) := by
  have key : ∀ {f' g' : S.X.presheaf.stalk P}, S.IsLocalEquation C.1 P f' →
      S.IsLocalEquation D.1 P g' → Ideal.span {f', g'} = Ideal.span {f, g} := by
    intro f' g' hf' hg'
    rw [Ideal.span_insert, Ideal.span_insert,
      Ideal.span_singleton_eq_span_singleton.2 (hf'.associated hf),
      Ideal.span_singleton_eq_span_singleton.2 (hg'.associated hg)]
  constructor
  · rintro ⟨f', g', hf', hg', h⟩
    rw [← key hf' hg', h]
  · exact fun h ↦ ⟨f, g, hf, hg, h⟩

namespace IsTransverseAt

variable {C D : S.Curve} {P : S.X} {f g : S.X.presheaf.stalk P}

/-- Generators of the maximal ideal lie in it. -/
private theorem mem_maximalIdeal_of_span_eq {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (h : Ideal.span {a, b} = maximalIdeal R) : a ∈ maximalIdeal R ∧ b ∈ maximalIdeal R :=
  ⟨h ▸ Ideal.subset_span (by simp), h ▸ Ideal.subset_span (by simp)⟩

/-- The local ring of the surface at a closed point is a regular local ring of dimension two,
so its cotangent space has dimension two. -/
private theorem finrank_cotangentSpace_eq_two (hP : IsClosed ({P} : Set S.X)) :
    Module.finrank (ResidueField (S.X.presheaf.stalk P)) (CotangentSpace (S.X.presheaf.stalk P))
      = 2 := by
  have : IsRegularLocalRing (S.X.presheaf.stalk P) := S.isRegular.2 P
  have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (S.X.presheaf.stalk P)).1 this
  rw [← dimension_at_closed_point S.hom S.finiteType P hP, S.dim_eq] at h
  exact_mod_cast h

/-- **Distinct embedded tangent lines.** If `C` and `D` meet transversally at a closed point `P`
with local equations `f, g`, then `f, g ∈ 𝔪_P` and their classes in the cotangent space
`𝔪_P/𝔪_P²` are linearly independent over the residue field `κ(P)`.

The embedded tangent line of `C` at `P` is the line in the Zariski tangent space
`T_P X = (𝔪_P/𝔪_P²)^∨` cut out by `df`, the class of `f` in `𝔪_P/𝔪_P²` (and similarly for `D`
with `dg`); these two lines are distinct exactly when `df` and `dg` are linearly independent, so
this encodes the statement that the embedded tangent lines of `C` and `D` at `P` are
distinct. -/
theorem linearIndependent_toCotangent (hP : IsClosed ({P} : Set S.X))
    (h : S.IsTransverseAt C D P) (hf : S.IsLocalEquation C.1 P f)
    (hg : S.IsLocalEquation D.1 P g) :
    ∃ (hfm : f ∈ maximalIdeal (S.X.presheaf.stalk P)) (hgm : g ∈ maximalIdeal (S.X.presheaf.stalk P)),
      LinearIndependent (ResidueField (S.X.presheaf.stalk P))
        ![(maximalIdeal (S.X.presheaf.stalk P)).toCotangent ⟨f, hfm⟩,
          (maximalIdeal (S.X.presheaf.stalk P)).toCotangent ⟨g, hgm⟩] := by
  have hspan := (isTransverseAt_iff hf hg).1 h
  obtain ⟨hfm, hgm⟩ := mem_maximalIdeal_of_span_eq hspan
  refine ⟨hfm, hgm, linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_⟩
  · have htop : Submodule.span (S.X.presheaf.stalk P)
        ({⟨f, hfm⟩, ⟨g, hgm⟩} : Set (maximalIdeal (S.X.presheaf.stalk P))) = ⊤ := by
      refine eq_top_iff.2 fun x _ ↦ ?_
      have hx : (x : S.X.presheaf.stalk P) ∈ Ideal.span {f, g} := by
        rw [hspan]; exact x.2
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hx
      have : x = a • ⟨f, hfm⟩ + b • ⟨g, hgm⟩ := Subtype.ext (by simp [hab])
      rw [this]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    rw [← CotangentSpace.span_image_eq_top_iff] at htop
    rw [← htop, Set.image_pair, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union]
  · rw [finrank_cotangentSpace_eq_two hP, Fintype.card_fin]

/-- The quotient of `𝒪_{X,P}` by one element whose class in `𝔪_P/𝔪_P²` is nonzero is regular. -/
private theorem isRegularLocalRing_quotient_of_ne_zero (a : maximalIdeal (S.X.presheaf.stalk P))
    (ha : (maximalIdeal (S.X.presheaf.stalk P)).toCotangent a ≠ 0) :
    IsRegularLocalRing (S.X.presheaf.stalk P ⧸ Ideal.span {(a : S.X.presheaf.stalk P)}) := by
  have : IsRegularLocalRing (S.X.presheaf.stalk P) := S.isRegular.2 P
  have h := isRegularLocalRing_quotient_span_range_of_linearIndependent (fun _ : Unit ↦ a)
    (LinearIndependent.of_subsingleton (i := ()) ha)
  rwa [Set.range_const] at h

/-- **`C` is regular at `P`.** If `C` and `D` meet transversally at a closed point `P` and `f` is
a local equation of `C` at `P`, then the local ring `𝒪_{C,P} = 𝒪_{X,P}/(f)` is a regular local
ring. -/
theorem isRegularLocalRing_left (hP : IsClosed ({P} : Set S.X)) (h : S.IsTransverseAt C D P)
    (hf : S.IsLocalEquation C.1 P f) :
    IsRegularLocalRing (S.X.presheaf.stalk P ⧸ Ideal.span {f}) := by
  obtain ⟨-, g, -, hg, -⟩ := id h
  obtain ⟨hfm, hgm, hli⟩ := linearIndependent_toCotangent hP h hf hg
  exact isRegularLocalRing_quotient_of_ne_zero ⟨f, hfm⟩ (by simpa using hli.ne_zero 0)

/-- **`D` is regular at `P`.** If `C` and `D` meet transversally at a closed point `P` and `g` is
a local equation of `D` at `P`, then the local ring `𝒪_{D,P} = 𝒪_{X,P}/(g)` is a regular local
ring. -/
theorem isRegularLocalRing_right (hP : IsClosed ({P} : Set S.X)) (h : S.IsTransverseAt C D P)
    (hg : S.IsLocalEquation D.1 P g) :
    IsRegularLocalRing (S.X.presheaf.stalk P ⧸ Ideal.span {g}) := by
  obtain ⟨f, -, hf, -, -⟩ := id h
  obtain ⟨hfm, hgm, hli⟩ := linearIndependent_toCotangent hP h hf hg
  exact isRegularLocalRing_quotient_of_ne_zero ⟨g, hgm⟩ (by simpa using hli.ne_zero 1)

/-- **The intersection has length one.** If `C` and `D` meet transversally at `P` with local
equations `f, g`, then the local ring `𝒪_{X,P}/(f, g)` of `C ∩ D` at `P` has length one. -/
theorem length_eq_one (h : S.IsTransverseAt C D P) (hf : S.IsLocalEquation C.1 P f)
    (hg : S.IsLocalEquation D.1 P g) :
    Module.length (S.X.presheaf.stalk P) (S.X.presheaf.stalk P ⧸ Ideal.span {f, g}) = 1 := by
  rw [(isTransverseAt_iff hf hg).1 h]
  have : IsSimpleModule (S.X.presheaf.stalk P)
      (S.X.presheaf.stalk P ⧸ maximalIdeal (S.X.presheaf.stalk P)) :=
    isSimpleModule_iff_isCoatom.2 (maximalIdeal.isMaximal _).out
  exact Module.length_eq_one _ _

/-- If `C` and `D` meet transversally at `P`, the local intersection multiplicity is
`(C.D)_P = 1`. -/
theorem localIntersectionMultiplicity_eq_one (h : S.IsTransverseAt C D P) :
    S.localIntersectionMultiplicity C D P = 1 := by
  obtain ⟨f, g, hf, hg, -⟩ := id h
  rw [localIntersectionMultiplicity_eq hf hg, length_eq_one h hf hg]

/-- **The intersection is reduced.** If `C` and `D` meet transversally at `P` with local
equations `f, g`, then the local ring `𝒪_{X,P}/(f, g)` of `C ∩ D` at `P` is reduced (it is the
residue field). -/
theorem isReduced (h : S.IsTransverseAt C D P) (hf : S.IsLocalEquation C.1 P f)
    (hg : S.IsLocalEquation D.1 P g) :
    IsReduced (S.X.presheaf.stalk P ⧸ Ideal.span {f, g}) := by
  rw [(isTransverseAt_iff hf hg).1 h]
  infer_instance

/-- **The intersection is a reduced `k`-point.** If `C` and `D` meet transversally at a closed
point `P` with local equations `f, g`, then `𝒪_{X,P}/(f, g) ≅ k`: the composite of the structure
map `k → 𝒪_{X,P}` with the quotient map `𝒪_{X,P} → 𝒪_{X,P}/(f, g)` is bijective. -/
theorem bijective_quotient_mk_comp_stalkStructureMap (hP : IsClosed ({P} : Set S.X))
    (h : S.IsTransverseAt C D P) (hf : S.IsLocalEquation C.1 P f)
    (hg : S.IsLocalEquation D.1 P g) :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {f, g})).comp (S.stalkStructureMap P)) := by
  have hspan := (isTransverseAt_iff hf hg).1 h
  have : (Ideal.span {f, g}).IsMaximal := hspan ▸ maximalIdeal.isMaximal _
  let _ : Field (S.X.presheaf.stalk P ⧸ Ideal.span {f, g}) := Ideal.Quotient.field _
  refine ⟨RingHom.injective _, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := surjective_residue_comp_stalkStructureMap hP (residue _ x)
  refine ⟨c, ?_⟩
  simp only [RingHom.comp_apply] at hc ⊢
  rw [Ideal.Quotient.eq, hspan]
  exact Ideal.Quotient.eq.1 hc

end IsTransverseAt

end

end Surface

end Hartshorne
