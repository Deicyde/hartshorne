/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.GenericCompletion
import Hartshorne.Scheme.RegularFunctionsSheaf
import Mathlib.Topology.Sheaves.Functors

/-!
# The regular-function sheaf on the generic completion

Hartshorne, *Algebraic Geometry*, II.2, the ringed space `(t(V), α_* 𝒪_V)` in
the proof of Proposition 2.6, p. 78.

For a variety `V`, the sheaf of regular functions is transported to the generic
completion `t(V)` along the order isomorphism between the opens of `V` and of
`t(V)`: the sections over an open `W` of `t(V)` are the regular functions on the
corresponding open of `V`, and the restriction maps are the usual restrictions
of functions.

## Main definitions and results

* `Hartshorne.genericCompletionRegularSheaf`: the transported sheaf of rings on
  `t(V)`. The sheaf condition comes from locality of regular functions.
* `Hartshorne.genericCompletionRegularSheaf_obj_eq_pushforward`: its underlying
  presheaf is the pushforward `α_* 𝒪_V`.
* `Hartshorne.genericCompletionRegularSectionsEquiv`: for an open `U` of `V`,
  the sections over the corresponding open of `t(V)` are canonically the
  regular functions on `U`;
  `Hartshorne.genericCompletionRegularSectionsEquiv_restrict` says this
  identification commutes with restriction, and
  `Hartshorne.genericCompletionRegularSectionsNatIso` packages both as a natural
  isomorphism of presheaves on `V`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace Hartshorne

universe u v

variable {k : Type u} [Field k] (V : Variety.{u, v} k)

/-- The presheaf of regular functions of `V`, transported to the generic
completion `t(V)` across the order isomorphism of opens: its sections over an
open `W` of `t(V)` are the regular functions on the corresponding open of `V`,
and its restriction maps are restrictions of functions. -/
def genericCompletionRegularPresheaf :
    (genericCompletionObj (TopCat.of V.carrier)).Presheaf CommRingCat.{max u v} where
  obj W := CommRingCat.of
    (V.regular ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm W.unop))
  map i := CommRingCat.ofHom (V.regularRestriction
    ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm.monotone i.unop.le))
  map_id _ := by
    ext f x
    rfl
  map_comp _ _ := by
    ext f x
    rfl

/-- The transported presheaf is the pushforward `α_* 𝒪_V` of the presheaf of
regular functions along `α : V → t(V)`. -/
theorem genericCompletionRegularPresheaf_eq_pushforward :
    genericCompletionRegularPresheaf V =
      genericCompletionAlpha (TopCat.of V.carrier) _* V.regularPresheaf :=
  rfl

/-- **Hartshorne II.2, p. 78.** The sheaf of rings on the generic completion
`t(V)` obtained by transporting the sheaf of regular functions of `V` across the
order isomorphism of opens. The sheaf condition follows from locality of
regular functions. -/
def genericCompletionRegularSheaf :
    (genericCompletionObj (TopCat.of V.carrier)).Sheaf CommRingCat.{max u v} := by
  refine ⟨genericCompletionRegularPresheaf V, ?_⟩
  rw [genericCompletionRegularPresheaf_eq_pushforward]
  apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (forget CommRingCat) V.regularPresheaf).mpr
  rw [Variety.regularPresheaf_comp_forget V]
  exact TopCat.subpresheafToTypes.isSheaf (Variety.regularLocalPredicate V)

/-- **Hartshorne II.2, p. 78.** The structure sheaf on `t(V)` is `α_* 𝒪_V`:
the underlying presheaf of the transported sheaf is the pushforward of the
presheaf of regular functions along `α`. -/
theorem genericCompletionRegularSheaf_obj_eq_pushforward :
    (genericCompletionRegularSheaf V).obj =
      genericCompletionAlpha (TopCat.of V.carrier) _* V.regularPresheaf :=
  rfl

@[simp]
theorem genericCompletionRegularSheaf_obj_obj
    (W : Opens (genericCompletionObj (TopCat.of V.carrier))) :
    (genericCompletionRegularSheaf V).obj.obj (op W) = CommRingCat.of
      (V.regular ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm W)) :=
  rfl

/-- Restriction in the transported sheaf is restriction of regular functions. -/
@[simp]
theorem genericCompletionRegularSheaf_map_apply
    {W W' : Opens (genericCompletionObj (TopCat.of V.carrier))} (h : W' ≤ W)
    (f : V.regular ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm W))
    (x : ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm W' : Opens V.carrier)) :
    ((genericCompletionRegularSheaf V).obj.map (homOfLE h).op f).1 x =
      f.1 ⟨x.1, (genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm.monotone h x.2⟩ :=
  rfl

/-- **Hartshorne II.2, p. 78.** For an open `U` of `V`, the sections of the
transported sheaf over the corresponding open of `t(V)` are canonically the
regular functions on `U`. -/
def genericCompletionRegularSectionsEquiv (U : Opens V.carrier) :
    (genericCompletionRegularSheaf V).obj.obj
        (op (genericCompletionOpensOrderIso (TopCat.of V.carrier) U)) ≃+*
      V.regular U :=
  have hU := (genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm_apply_apply U
  { toFun := V.regularRestriction hU.ge
    invFun := V.regularRestriction hU.le
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' := map_mul _
    map_add' := map_add _ }

@[simp]
theorem genericCompletionRegularSectionsEquiv_apply (U : Opens V.carrier)
    (f : (genericCompletionRegularSheaf V).obj.obj
      (op (genericCompletionOpensOrderIso (TopCat.of V.carrier) U))) (x : U) :
    (genericCompletionRegularSectionsEquiv V U f).1 x =
      f.1 ⟨x.1, ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm_apply_apply U).ge
        x.2⟩ :=
  rfl

/-- **Hartshorne II.2, p. 78.** The identification of sections on corresponding
opens commutes with restriction. -/
theorem genericCompletionRegularSectionsEquiv_restrict {U U' : Opens V.carrier} (h : U' ≤ U)
    (f : (genericCompletionRegularSheaf V).obj.obj
      (op (genericCompletionOpensOrderIso (TopCat.of V.carrier) U))) :
    genericCompletionRegularSectionsEquiv V U'
        ((genericCompletionRegularSheaf V).obj.map
          (homOfLE ((genericCompletionOpensOrderIso (TopCat.of V.carrier)).monotone h)).op f) =
      V.regularRestriction h (genericCompletionRegularSectionsEquiv V U f) :=
  rfl

/-- The identification of sections on corresponding opens as a natural
isomorphism: pulling the transported sheaf back along the order isomorphism of
opens gives the presheaf of regular functions of `V`. -/
def genericCompletionRegularSectionsNatIso :
    (genericCompletionOpensOrderIso (TopCat.of V.carrier)).monotone.functor.op ⋙
        (genericCompletionRegularSheaf V).obj ≅ V.regularPresheaf :=
  NatIso.ofComponents
    (fun U => (genericCompletionRegularSectionsEquiv V U.unop).toCommRingCatIso)
    (fun _ => by
      ext f
      rfl)

end Hartshorne
