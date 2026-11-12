/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SymmetricAlgebraSheaf
import Hartshorne.Scheme.ExteriorPerfectPairing

/-!
# Sections of the polynomial algebra sheaf over quasi-compact opens

Supplements Hartshorne II, Exercise 5.18(a) (p. 128). On a ringed space `(X, 𝒪_X)`, the
polynomial algebra sheaf `𝒪_X[T_i]` is the sheafification of the presheaf
`U ↦ 𝒪_X(U)[T_i]` (`polynomialAlgebraSheaf`). This presheaf is separated, so the canonical map
`𝒪_X(U)[T_i] → 𝒪_X[T_i](U)` is injective for every open `U`
(`sheafifyUnit_polynomialPresheaf_injective`); over a quasi-compact open `U` it is bijective
(`sheafifyUnit_polynomialPresheaf_bijective`): a section of the sheafification is locally a
polynomial, finitely many such local polynomials suffice, and their coefficients glue.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne

open SheafAlgebraOperations

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ι : Type u)

/-- Polynomials over `𝒪_X(U)` whose coefficients agree locally are equal. -/
lemma mvPolynomial_ext_of_locally {U : Opens X}
    (p q : MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)))
    (h : ∀ x ∈ U, ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U),
      MvPolynomial.map ((R.obj ⋙ forget₂ CommRingCat RingCat).map i.op).hom p =
        MvPolynomial.map ((R.obj ⋙ forget₂ CommRingCat RingCat).map i.op).hom q) :
    p = q := by
  ext m
  refine TopCat.Presheaf.section_ext (R : TopCat.Sheaf CommRingCat X) U _ _ fun x hx => ?_
  obtain ⟨V, hxV, i, e⟩ := h x hx
  rw [← TopCat.Presheaf.germ_res_apply _ i x hxV, ← TopCat.Presheaf.germ_res_apply _ i x hxV]
  congr 1
  have := congrArg (MvPolynomial.coeff m) e
  rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at this

variable {ι} {P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} {U : Opens X}
  (ρ : ∀ W : Opens X, W ≤ U →
    MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op W)) → P.obj (op W))
  (hρ : ∀ W h, Function.Bijective (ρ W h))
  (hρmap : ∀ (W W' : Opens X) (h : W ≤ U) (h' : W' ≤ W) p,
    P.map (homOfLE h').op (ρ W h p) =
      ρ W' (h'.trans h) (MvPolynomial.map ((R.obj ⋙ forget₂ CommRingCat RingCat).map
        (homOfLE h').op).hom p))

include hρ hρmap in
/-- **A presheaf which is polynomial over `U` is separated over `U`**: if over every open `W ⊆ U`
the sections `P(W)` are identified with `𝒪_X(W)[T_i]`, compatibly with restriction, then the
canonical map from `P(W)` to the sections of the sheafification is injective. -/
theorem sheafifyUnit_injective_of_polynomial {W : Opens X} (hW : W ≤ U) :
    Function.Injective ((sheafifyUnit P).app (op W)) := by
  intro p q hpq
  obtain ⟨p, rfl⟩ := (hρ W hW).2 p
  obtain ⟨q, rfl⟩ := (hρ W hW).2 q
  congr 1
  refine mvPolynomial_ext_of_locally ι p q fun x hx => ?_
  have hgerm : Ringed.stalkAddMap (sheafifyUnit P) x
      (ModuleSheafTensor.sectionGerm _ x W hx (ρ W hW p)) =
      Ringed.stalkAddMap (sheafifyUnit P) x (ModuleSheafTensor.sectionGerm _ x W hx (ρ W hW q)) := by
    rw [Ringed.stalkAddMap_germ, Ringed.stalkAddMap_germ, hpq]
  obtain ⟨V, hV, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq P.presheaf x hx hx
    _ _ ((stalkMap_sheafifyUnit_bijective _ x).1 hgerm)
  rw [Subsingleton.elim i₂ i₁] at e
  refine ⟨V, hV, i₁, (hρ V (i₁.le.trans hW)).1 ?_⟩
  have e' : P.map (homOfLE i₁.le).op (ρ W hW p) = P.map (homOfLE i₁.le).op (ρ W hW q) := e
  rwa [hρmap, hρmap] at e'

open Classical in
private lemma coeff_sum_monomial {A : Type u} [CommSemiring A] (T : Finset (ι →₀ ℕ))
    (c : (ι →₀ ℕ) → A) (m : ι →₀ ℕ) :
    MvPolynomial.coeff m (∑ n ∈ T, MvPolynomial.monomial n (c n)) = if m ∈ T then c m else 0 := by
  classical
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  exact Finset.sum_ite_eq' T m c

include hρ hρmap in
/-- **A presheaf which is polynomial over a quasi-compact open `U` has the same sections over `U`
as its sheafification**: if over every open `W ⊆ U` the sections `P(W)` are identified with
`𝒪_X(W)[T_i]`, compatibly with restriction, then the canonical map from `P(U)` to the sections of
the sheafification is bijective. A section of the sheafification is locally the image of a local
polynomial; finitely many suffice, and their finitely many nonzero coefficients glue. -/
theorem sheafifyUnit_bijective_of_polynomial (hU : IsCompact (U : Set X)) :
    Function.Bijective ((sheafifyUnit P).app (op U)) := by
  classical
  refine ⟨sheafifyUnit_injective_of_polynomial ρ hρ hρmap le_rfl, fun s => ?_⟩
  let A := fun V : Opens X => MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
  choose V hxV i p hp using fun x : U => exists_unit_eq_map P s x.2
  choose p' hp' using fun x : U => (hρ (V x) (i x).le).2 (p x)
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV _⟩)
  -- the local polynomials agree on overlaps
  have hcompat : ∀ x y : U,
      MvPolynomial.map ((R.obj ⋙ forget₂ CommRingCat RingCat).map
        (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)).op).hom (p' x) =
      MvPolynomial.map ((R.obj ⋙ forget₂ CommRingCat RingCat).map
        (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)).op).hom (p' y) := by
    intro x y
    have hle : V x ⊓ V y ≤ U := inf_le_left.trans (i x).le
    apply (hρ _ hle).1
    have h1 := hρmap (V x) (V x ⊓ V y) (i x).le inf_le_left (p' x)
    have h2 := hρmap (V y) (V x ⊓ V y) (i y).le inf_le_right (p' y)
    refine h1.symm.trans (Eq.trans ?_ h2)
    apply sheafifyUnit_injective_of_polynomial ρ hρ hρmap hle
    rw [hp', hp', PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hp, hp,
      ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) s
  let T : Finset (ι →₀ ℕ) := t.biUnion fun x => (p' x).support
  -- glue the coefficients of each monomial
  have hglue : ∀ m : ι →₀ ℕ, ∃ c : (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U),
      ∀ x : t, R.obj.map (i x).op c = MvPolynomial.coeff m (p' x) := by
    intro m
    obtain ⟨c, hc, -⟩ := TopCat.Sheaf.existsUnique_gluing' (R : TopCat.Sheaf CommRingCat X)
      (fun x : t => V x) U (fun x => i x)
      (fun y hy => by
        obtain ⟨x, ⟨hx, hyx⟩⟩ : ∃ x ∈ t, y ∈ V x := by
          simpa using ht hy
        exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hyx⟩)
      (fun x => MvPolynomial.coeff m (p' x))
      (fun x y => by
        have := congrArg (MvPolynomial.coeff m) (hcompat x y)
        rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at this)
    exact ⟨c, hc⟩
  choose c hc using hglue
  let q : A U := ∑ m ∈ T, MvPolynomial.monomial m (c m)
  have hcoeff : ∀ x : t, P.map (i x).op (ρ U le_rfl q) = p x := by
    intro x
    rw [Subsingleton.elim (i x) (homOfLE (i x).le), hρmap, ← hp']
    congr 1
    ext m
    rw [MvPolynomial.coeff_map]
    by_cases hm : m ∈ T
    · rw [show MvPolynomial.coeff m q = c m from (coeff_sum_monomial T c m).trans (if_pos hm)]
      exact hc m x
    · have h1 : MvPolynomial.coeff m q = 0 := (coeff_sum_monomial T c m).trans (if_neg hm)
      have h2 : MvPolynomial.coeff m (p' x) = 0 := by
        by_contra h
        exact hm (Finset.mem_biUnion.mpr ⟨x, x.2, MvPolynomial.mem_support_iff.mpr h⟩)
      rw [h1, h2, map_zero]
  refine ⟨ρ U le_rfl q, sheaf_section_ext _ _ _ fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ : ∃ x ∈ t, y ∈ V x := by simpa using ht hy
  refine ⟨V x, hyx, i x, ?_⟩
  rw [← hp x, ← hcoeff ⟨x, hx⟩]
  exact (PresheafOfModules.naturality_apply (sheafifyUnit P) (i x).op _).symm

section SymmetricAlgebra

open SheafTensorOperations

variable {E : SheafOfModules.{u} (ringCatSheafOf R)} {κ : Type u} [Fintype κ] [DecidableEq κ]
  {U : Opens X} {e : κ → E.val.obj (op U)}

/-- The identification `𝒪_X(W)[T_k] ≅ S(E(W))`, `T_k ↦ e_k|_W`, over an open `W ⊆ U`, for a frame
`e` of `E` over `U`. -/
noncomputable def frameSymmetricAlgebraEquiv (he : Ringed.IsLocalFrame E U e) {W : Opens X}
    (h : W ≤ U) :
    MvPolynomial κ ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op W)) ≃ₐ[
      (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op W)]
      SymmetricAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op W)) (E.val.obj (op W)) :=
  (SymmetricAlgebra.equivMvPolynomial (ExteriorPerfectPairing.frameBasis E he h)).symm

lemma frameSymmetricAlgebraEquiv_X (he : Ringed.IsLocalFrame E U e) {W : Opens X} (h : W ≤ U)
    (k : κ) :
    frameSymmetricAlgebraEquiv he h (MvPolynomial.X k) =
      SymmetricAlgebra.ι _ _ (E.val.map (homOfLE h).op (e k)) := by
  rw [frameSymmetricAlgebraEquiv, SymmetricAlgebra.equivMvPolynomial_symm_X,
    ExteriorPerfectPairing.frameBasis_apply]
  rfl

/-- **Over a quasi-compact open on which `E` has a frame, `S(E)` has the sections `S(E(U))`**: the
canonical map `S(E(U)) → S(E)(U)` is bijective. -/
theorem moduleSheafSymmetricAlgebra_sheafifyUnit_bijective (he : Ringed.IsLocalFrame E U e)
    (hU : IsCompact (U : Set X)) :
    Function.Bijective ((sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf E)).app (op U)) := by
  refine sheafifyUnit_bijective_of_polynomial (fun W h => frameSymmetricAlgebraEquiv he h)
    (fun W h => (frameSymmetricAlgebraEquiv he h).bijective) (fun W W' h h' p => ?_) hU
  refine (equivMvPolynomial_symm_map _ (E.val.restrictₛₗ (homOfLE h').op) _ _ (fun k => ?_) p).symm
  rw [ExteriorPerfectPairing.frameBasis_apply, ExteriorPerfectPairing.frameBasis_apply]
  change E.val.map (homOfLE h').op (E.val.map (homOfLE h).op (e k)) =
    E.val.map (homOfLE (h'.trans h)).op (e k)
  rw [← PresheafOfModules.map_comp_apply]
  rfl

end SymmetricAlgebra

end Hartshorne
