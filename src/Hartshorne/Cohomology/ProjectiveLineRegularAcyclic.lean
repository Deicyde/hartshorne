/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ProjectiveLinePrincipalParts
import Hartshorne.Cohomology.SheafCohomologyFlasque
import Hartshorne.Cohomology.SheafCohomologyLongExactSequence

/-!
# Acyclicity of the sheaf of regular functions on `ℙ¹`

Hartshorne, *Algebraic Geometry*, III, Exercise 2.2 (p. 212), with II, Exercise 1.21(d,e).

Let `X = ℙ¹` be the projective line over an algebraically closed field `k`, as a variety with its
sheaf of regular functions `𝒪_X`. Then `H^i(X, 𝒪_X) = 0` for every `i > 0`
(`Hartshorne.projectiveLine_sheafCohomology_regular_isZero`).

## Proof

The principal-parts resolution `0 → 𝒪_X → K_X → ⨁_{P} i_{P,*}(K/𝒪_{X,P}) → 0` is a short exact
sequence whose last map is surjective on global sections. The constant sheaf `K_X` is flasque
because `X` is irreducible (`Hartshorne.isFlasque_constantSheaf_of_irreducibleSpace`), and the
locally finite sum of skyscrapers is flasque because `X` is Noetherian
(`Hartshorne.isFlasque_locallyFiniteSumSheaf`). Flasque sheaves are acyclic, so the long exact
sequence gives `H^1(X, 𝒪_X) = coker(Γ(K_X) → Γ(⨁ i_{P,*}(K/𝒪_{X,P}))) = 0` and
`H^i(X, 𝒪_X) = 0` for `i ≥ 2`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Hartshorne

universe u

/-- The constant sheaf on an irreducible space is flasque: on a nonempty open set its sections are
constant. -/
theorem isFlasque_constantSheaf_of_irreducibleSpace (X : TopCat.{u}) [IrreducibleSpace X]
    (A : AddCommGrpCat.{u}) : (constantSheaf X A).IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    change LocallyConstant V.unop A at t
    by_cases hV : (V.unop : Set X).Nonempty
    · obtain ⟨x, hx⟩ := hV
      have hpre : IsPreconnected (V.unop : Set X) :=
        ((IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset V.unop.isOpen
          (Set.subset_univ _)).isPreconnected
      have : PreconnectedSpace V.unop := Subtype.preconnectedSpace hpre
      refine ⟨(LocallyConstant.const U.unop (t ⟨x, hx⟩) : LocallyConstant U.unop A), ?_⟩
      change LocallyConstant.comap _ (LocallyConstant.const U.unop (t ⟨x, hx⟩)) = t
      ext y
      exact (t.apply_eq_of_preconnectedSpace y ⟨x, hx⟩).symm
    · refine ⟨(0 : LocallyConstant U.unop A), ?_⟩
      change LocallyConstant.comap _ (0 : LocallyConstant U.unop A) = t
      ext y
      exact absurd ⟨y.1, y.2⟩ hV

/-- On a Noetherian space the locally finite sum of skyscraper sheaves is flasque: a section over
`V ⊆ U` has finite support, so it extends by zero to `U`. -/
theorem isFlasque_locallyFiniteSumSheaf {X : TopCat.{u}} [NoetherianSpace X]
    (A : X → AddCommGrpCat.{u}) : (locallyFiniteSumSheaf A).IsFlasque where
  epi {U V} i := by
    classical
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    have hfin := LocallyFiniteSupport.finite A t.2
    let s : ∀ x : U.unop, A x := fun x ↦ if h : x.1 ∈ V.unop then t.1 ⟨x.1, h⟩ else 0
    have hs : LocallyFiniteSupport A s := by
      intro x
      refine ⟨⊤, trivial, ?_⟩
      refine (hfin.image (fun y : V.unop ↦ (⟨y.1, leOfHom i.unop y.2⟩ : U.unop))).subset ?_
      rintro y ⟨-, hy⟩
      simp only [s] at hy
      split_ifs at hy with h
      · exact ⟨⟨y.1, h⟩, hy, rfl⟩
      · exact absurd rfl hy
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    funext x
    change s ⟨x.1, leOfHom i.unop x.2⟩ = t.1 x
    simp only [s, dif_pos x.2]

/-- **Acyclicity of `𝒪` on the projective line** (Hartshorne III, Exercise 2.2). For the projective
line `X = ℙ¹` over an algebraically closed field, `H^i(X, 𝒪_X) = 0` for every `i > 0`. -/
theorem projectiveLine_sheafCohomology_regular_isZero (k : Type u) [Field k] [IsAlgClosed k]
    (i : ℕ) (hi : 0 < i) :
    IsZero ((sheafCohomology (TopCat.of (projectiveLine k).carrier) i).obj
      (projectiveLine k).regularAbSheaf) := by
  have : NoetherianSpace (projectiveLine k).carrier :=
    NoetherianSpace.set (Set.univ : Set (ProjectiveSpace k (Fin 2)))
  have : IrreducibleSpace (projectiveLine k).carrier := (projectiveLine k).irreducible
  obtain ⟨-, hS, hsurj⟩ := projectiveLine_principalPartsResolution k
  set S := (projectiveLine k).principalPartsComplex (projectiveLine_finite_of_isClosed (k := k))
  have hK : S.X₂.IsFlasque :=
    isFlasque_constantSheaf_of_irreducibleSpace (TopCat.of (projectiveLine k).carrier) _
  have hP : S.X₃.IsFlasque := isFlasque_locallyFiniteSumSheaf _
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rcases n with _ | n
  · -- `H^0(K_X) ⟶ H^0(⨁ i_{P,*}(K/𝒪_{X,P}))` is surjective, so the connecting map vanishes.
    have hepi : Epi ((sheafCohomology (TopCat.of (projectiveLine k).carrier) 0).map S.g) := by
      have hnat := (sheafCohomologyZeroIso (TopCat.of (projectiveLine k).carrier)).hom.naturality
        S.g
      have hΓ : Epi ((sheafSectionsOver (X := TopCat.of (projectiveLine k).carrier) ⊤).map S.g) :=
        (AddCommGrpCat.epi_iff_surjective _).2 hsurj
      have h : (sheafCohomology (TopCat.of (projectiveLine k).carrier) 0).map S.g =
          (sheafCohomologyZeroIso (TopCat.of (projectiveLine k).carrier)).hom.app S.X₂ ≫
            (sheafSectionsOver (X := TopCat.of (projectiveLine k).carrier) ⊤).map S.g ≫
              (sheafCohomologyZeroIso (TopCat.of (projectiveLine k).carrier)).inv.app S.X₃ := by
        rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      rw [h]
      infer_instance
    have hδ : sheafCohomologyδ hS 0 = 0 :=
      (sheafCohomology_exact₃ hS 0).epi_f_iff.1 hepi
    refine (sheafCohomology_exact₁ hS 0).isZero_X₂ hδ ?_
    exact (sheafCohomology_isZero_of_isFlasque S.X₂ 0).eq_of_tgt _ _
  · exact (sheafCohomology_exact₁ hS (n + 1)).isZero_of_both_isZero
      (sheafCohomology_isZero_of_isFlasque S.X₃ n)
      (sheafCohomology_isZero_of_isFlasque S.X₂ (n + 1))

end Hartshorne
