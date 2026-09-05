/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyLocalRingHom
import Hartshorne.Morphism.ProjVariety

/-!
# The local ring does not see beyond an open neighbourhood

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(b) and (c).

If `Z ⊆ Y` are quasi-projective and `Z` is open in `Y`, the inclusion is a
morphism of varieties, and for `P ∈ Z` it induces an isomorphism
`𝒪_{P,Y} ≅ 𝒪_{P,Z}`.

Hartshorne uses this silently. Theorem 3.4(b) is about `𝒪_P` for a projective
`Y`, and the proof works on the affine piece `Yᵢ = Y ∩ Uᵢ`; that the two local
rings are the same ring is what licenses the move, and it is the only step of
3.4(b) that is about germs rather than about coordinates.

Both halves come from work already done. Injectivity is the identity principle:
two germs agreeing on a neighbourhood of `P` inside `Z` agree on the whole
overlap of their domains, because `Z` meets that overlap in a nonempty open set
and a variety is irreducible. Surjectivity pushes a germ forward, which needs
only that an open subset of `Z` is an open subset of `Y`.

## Main definitions

* `Hartshorne.inclHom`, `Hartshorne.pushGerm`

## Main results

* `Hartshorne.bijective_localRingHom_inclHom`
-/

namespace Hartshorne

open TopologicalSpace MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} {Y Z : Set (ProjectiveSpace k σ)}
  (hY : IsQuasiProjVariety Y) (hZ : IsQuasiProjVariety Z) (hZY : Z ⊆ Y)

/-- The inclusion of one quasi-projective set in another is a morphism of
varieties. Regularity is a condition on the map to projective space, and that
map is the same one on both sides. -/
noncomputable def inclHom :
    VarietyHom (Variety.ofQuasiProjective hZ) (Variety.ofQuasiProjective hY) where
  toFun x := ⟨x.1, hZY x.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  regular_comp V f hf := by
    intro Q
    have hcont : Continuous fun x : (Opens.comap
        ⟨fun x : Z => (⟨x.1, hZY x.2⟩ : Y), Continuous.subtype_mk continuous_subtype_val _⟩ V) =>
        (⟨⟨x.1.1, hZY x.1.2⟩, x.2⟩ : V) := by fun_prop
    obtain ⟨W, hW, hQW, n, g, h, hg, hh, hne, he⟩ :=
      (mem_projRegularSubalgebra.1 hf) ⟨⟨Q.1.1, hZY Q.1.2⟩, Q.2⟩
    exact ⟨_, hW.preimage hcont, hQW, n, g, h, hg, hh,
      fun x hx => hne ⟨⟨x.1.1, hZY x.1.2⟩, x.2⟩ hx,
      fun x hx => he ⟨⟨x.1.1, hZY x.1.2⟩, x.2⟩ hx⟩

variable (hopen : IsOpen {y : Y | y.1 ∈ Z})

include hopen in
/-- An open subset of `Z` is an open subset of `Y`.

`U` is cut out of `Z` by an open set of projective space, and `Z` is cut out of
`Y` by an open set of `Y`; the two conditions intersect. -/
theorem isOpen_pushOpens (U : Opens (Variety.ofQuasiProjective hZ).carrier) :
    IsOpen {y : Y | ∃ h : y.1 ∈ Z, (⟨y.1, h⟩ : Z) ∈ U} := by
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 U.isOpen
  have hmem : ∀ z : (Variety.ofQuasiProjective hZ).carrier, z ∈ U ↔ z.1 ∈ O := by
    intro z
    simp only [← SetLike.mem_coe, ← hOU]
    exact Iff.rfl
  have hset : {y : Y | ∃ h : y.1 ∈ Z, (⟨y.1, h⟩ : Z) ∈ U}
      = {y : Y | y.1 ∈ Z} ∩ Subtype.val ⁻¹' O := by
    ext y
    exact ⟨fun ⟨h, hU⟩ => ⟨h, (hmem _).1 hU⟩, fun ⟨h, hOy⟩ => ⟨h, (hmem ⟨y.1, h⟩).2 hOy⟩⟩
  rw [hset]
  exact hopen.inter (hO.preimage continuous_subtype_val)

section Push

variable {U : Opens (Variety.ofQuasiProjective hZ).carrier}
  {V : Opens (Variety.ofQuasiProjective hY).carrier}
  (hV : ∀ y : (Variety.ofQuasiProjective hY).carrier,
    y ∈ V ↔ ∃ h : y.1 ∈ Z, (⟨y.1, h⟩ : Z) ∈ U)

/-- The point of `U` underlying a point of `V`.

It is `Subtype.val` twice over, but the membership proof in the middle has to be
pulled out of an existential, so it is not literally that. `V` is carried as a
variable described by `hV`, rather than as the set itself: instance search will
not unfold a definition to see that `↥V` is a subtype, so naming the pushed-open
set makes `Continuous` unstatable. -/
noncomputable def pullPoint (y : V) : U :=
  ⟨⟨y.1.1, ((hV y.1).1 y.2).choose⟩, ((hV y.1).1 y.2).choose_spec⟩

theorem continuous_pullPoint : Continuous fun y : V => pullPoint hY hZ hV y := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact continuous_subtype_val.comp continuous_subtype_val

/-- Regularity survives the view of an open subset of `Z` as an open subset of
`Y`: the condition is about the map to projective space, which is unchanged. -/
theorem regular_pullPoint (f : U → k) (hf : f ∈ (Variety.ofQuasiProjective hZ).regular U) :
    (fun y => f (pullPoint hY hZ hV y)) ∈ (Variety.ofQuasiProjective hY).regular V := by
  intro Q
  obtain ⟨W, hW, hQW, n, g, h, hg, hh, hne, he⟩ :=
    (mem_projRegularSubalgebra.1 hf) (pullPoint hY hZ hV Q)
  exact ⟨_, hW.preimage (continuous_pullPoint hY hZ hV), hQW, n, g, h, hg, hh,
    fun x hx => hne (pullPoint hY hZ hV x) hx, fun x hx => he (pullPoint hY hZ hV x) hx⟩

end Push

variable {hZY} in
/-- Pushing a germ at `P ∈ Z` forward to a germ at `P ∈ Y`. -/
noncomputable def pushGerm {P : (Variety.ofQuasiProjective hZ).carrier}
    (t : Variety.GermRep (Variety.ofQuasiProjective hZ) P) :
    Variety.GermRep (Variety.ofQuasiProjective hY) (inclHom hY hZ hZY P) where
  U := ⟨_, isOpen_pushOpens hZ hopen t.U⟩
  mem_U := ⟨P.2, t.mem_U⟩
  toFun := fun y => t.toFun (pullPoint hY hZ (U := t.U)
    (V := ⟨_, isOpen_pushOpens hZ hopen t.U⟩) (fun _ => Iff.rfl) y)
  regular := regular_pullPoint hY hZ (fun _ => Iff.rfl) t.toFun t.regular

include hopen in
/-- **The local ring does not see beyond an open neighbourhood.**

Injectivity is the identity principle: two germs on `Y` whose restrictions to
`Z` agree agree on the overlap of their domains, since `Z` meets that overlap in
a nonempty open set. Surjectivity is `pushGerm`. -/
theorem bijective_localRingHom_inclHom (P : (Variety.ofQuasiProjective hZ).carrier) :
    Function.Bijective ((inclHom hY hZ hZY).localRingHom P) := by
  constructor
  · refine Quotient.ind fun r => Quotient.ind fun s => fun hrs => ?_
    have hrel := Quotient.exact hrs
    refine Quotient.sound ?_
    -- Compare the two functions on the overlap of the domains.
    set U : Opens (Variety.ofQuasiProjective hY).carrier := r.U ⊓ s.U with hU
    have hfr : (fun x : U => r.toFun ⟨x.1, x.2.1⟩) ∈ (Variety.ofQuasiProjective hY).regular U :=
      (Variety.ofQuasiProjective hY).regular_restrict inf_le_left r.regular
    have hfs : (fun x : U => s.toFun ⟨x.1, x.2.2⟩) ∈ (Variety.ofQuasiProjective hY).regular U :=
      (Variety.ofQuasiProjective hY).regular_restrict inf_le_right s.regular
    have hVopen : IsOpen {x : U | x.1.1 ∈ Z} := hopen.preimage continuous_subtype_val
    have hPU : (⟨inclHom hY hZ hZY P, r.mem_U, s.mem_U⟩ : U) ∈ {x : U | x.1.1 ∈ Z} := P.2
    have heq := Variety.eq_of_eqOn hfr hfs hVopen ⟨_, hPU⟩ fun x hx =>
      hrel ⟨x.1.1, hx⟩ x.2.1 x.2.2
    exact fun y hr hs => congrFun heq ⟨y, hr, hs⟩
  · refine Quotient.ind fun t => ?_
    exact ⟨Quotient.mk _ (pushGerm hY hZ hopen t), Quotient.sound fun x _ _ => rfl⟩

end Hartshorne
