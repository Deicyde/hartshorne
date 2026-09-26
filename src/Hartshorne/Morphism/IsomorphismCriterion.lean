/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyLocalRingHom

/-!
# A local criterion for isomorphisms of varieties

Hartshorne, *Algebraic Geometry*, Chapter I, Exercise 3.3(b).

A morphism of varieties is an isomorphism exactly when its underlying map is a
homeomorphism and its pullback maps on all local rings are bijective.  For the
reverse implication, only surjectivity of the local-ring maps is needed:
locally lift each regular-function germ through the map on local rings, then
use the homeomorphism to pull the resulting neighbourhood back to the source.
-/

namespace Hartshorne

open TopologicalSpace

noncomputable section

universe u v

variable {k : Type u} [Field k] {X Y : Variety.{u, v} k}

namespace VarietyHom

/-- An isomorphism of varieties is a homeomorphism on the underlying spaces. -/
theorem IsIso.isHomeomorph {f : VarietyHom X Y} (hf : f.IsIso) :
    IsHomeomorph f.toFun := by
  have hbijective := hf.bijective
  obtain ⟨g, hgf, hfg⟩ := hf
  refine ⟨f.continuous_toFun, IsOpenMap.of_inverse g.continuous_toFun ?_ ?_, hbijective⟩
  · intro y
    have h := congrArg (fun (φ : VarietyHom Y Y) => φ.toFun y) hfg
    simpa using h
  · intro x
    have h := congrArg (fun (φ : VarietyHom X X) => φ.toFun x) hgf
    simpa using h

/-- A homeomorphic morphism that is surjective on every local ring is an
isomorphism. -/
theorem isIso_of_isHomeomorph_of_surjective_localRingHom
    (f : VarietyHom X Y) (hf : IsHomeomorph f.toFun)
    (hlocal : ∀ P : X.carrier, Function.Surjective (f.localRingHom P)) :
    f.IsIso := by
  let e : X.carrier ≃ₜ Y.carrier := IsHomeomorph.homeomorph f.toFun hf
  let g : VarietyHom Y X :=
    { toFun := e.symm
      continuous_toFun := e.symm.continuous
      regular_comp := by
        intro U h hreg
        apply Y.regular_of_locally
        intro y
        let x : X.carrier := e.symm y.1
        let rX : X.GermRep x :=
          { U := U
            mem_U := y.2
            toFun := h
            regular := hreg }
        obtain ⟨a, ha⟩ := hlocal x
          (Quotient.mk (Variety.germSetoid X x) rX)
        let rY : Y.GermRep (f x) := Quotient.out a
        have hrY :
            (Quotient.mk (Variety.germSetoid Y (f x)) rY :
              Y.LocalRingAt (f x)) = a :=
          Quotient.out_eq a
        have hrel : (f.germPullback x rY).Rel rX := by
          have hquot : f.localRingHom x
              (Quotient.mk (Variety.germSetoid Y (f x)) rY) =
                Quotient.mk (Variety.germSetoid X x) rX := by
            rw [hrY]
            exact ha
          exact @Quotient.exact (X.GermRep x) (Variety.germSetoid X x)
            (f.germPullback x rY) rX hquot
        let W : Opens Y.carrier :=
          Opens.comap ⟨e.symm, e.symm.continuous⟩ U
        let N : Opens Y.carrier := W ⊓ rY.U
        have hNW : N ≤ W := inf_le_left
        have hyfx : f x = y.1 := by
          change e (e.symm y.1) = y.1
          exact e.apply_symm_apply y.1
        have hyrY : y.1 ∈ rY.U := by
          simpa only [hyfx] using rY.mem_U
        have hyN : y.1 ∈ N := ⟨y.2, hyrY⟩
        refine ⟨N, hNW, hyN, ?_⟩
        change (fun z : N => h ⟨e.symm z.1, z.2.1⟩) ∈ Y.regular N
        convert Y.regular_restrict (show N ≤ rY.U from inf_le_right) rY.regular using 1
        funext z
        have hzfg : f (e.symm z.1) = z.1 := by
          change e (e.symm z.1) = z.1
          exact e.apply_symm_apply z.1
        have hzU : f (e.symm z.1) ∈ rY.U := by
          rw [hzfg]
          exact z.2.2
        have hzpullback : e.symm z.1 ∈ (f.germPullback x rY).U := by
          exact hzU
        have hzrel := hrel (e.symm z.1) hzpullback z.2.1
        change rY.toFun ⟨f (e.symm z.1), hzU⟩ =
          h ⟨e.symm z.1, z.2.1⟩ at hzrel
        calc
          h ⟨e.symm z.1, z.2.1⟩ =
              rY.toFun ⟨f (e.symm z.1), hzU⟩ := hzrel.symm
          _ = rY.toFun ⟨z.1, z.2.2⟩ := by
            congr }
  refine ⟨g, ?_, ?_⟩
  · apply VarietyHom.ext
    funext x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  · apply VarietyHom.ext
    funext y
    change e (e.symm y) = y
    exact e.apply_symm_apply y

/-- **Hartshorne I, Exercise 3.3(b).** A morphism of varieties is an
isomorphism if and only if it is a homeomorphism and induces an isomorphism on
the local ring at every point. -/
theorem isIso_iff_isHomeomorph_and_bijective_localRingHom
    (f : VarietyHom X Y) :
    f.IsIso ↔
      IsHomeomorph f.toFun ∧
        ∀ P : X.carrier, Function.Bijective (f.localRingHom P) := by
  constructor
  · intro hf
    exact ⟨hf.isHomeomorph, fun P => bijective_localRingHom_of_isIso hf P⟩
  · rintro ⟨hf, hlocal⟩
    exact isIso_of_isHomeomorph_of_surjective_localRingHom f hf fun P => (hlocal P).2

end VarietyHom

end

end Hartshorne
