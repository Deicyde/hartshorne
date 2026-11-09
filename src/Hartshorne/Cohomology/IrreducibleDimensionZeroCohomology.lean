/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SheafCohomology
import Hartshorne.Cohomology.CohomologyWithSupports
import Mathlib.Topology.KrullDimension

/-!
# Cohomology of an irreducible space of dimension zero

Hartshorne, *Algebraic Geometry*, III.2, proof of Theorem 2.7, Step 2 (p. 210): if `X` is an
irreducible noetherian space of dimension `0`, then the only open subsets of `X` are `∅` and `X`,
so the global section functor `Γ(X,-)` is exact
(`Hartshorne.preservesFiniteColimits_sheafSectionsOver_top_of_irreducible_dim_zero`) and
`H^i(X,F) = 0` for every abelian sheaf `F` and every `i > 0`
(`Hartshorne.sheafCohomology_isZero_of_irreducible_dim_zero`).

The noetherian hypothesis of the source is not needed for either statement.

Proof: every point of `X` is a generic point (its closure is an irreducible closed subset, maximal
because `dim X = 0`), so a nonempty open subset contains a point specialising to every point and
is all of `X`. Hence every abelian sheaf on `X` is flasque (its sections over `∅` vanish), so
`Γ(X,-)` sends short exact sequences to short exact sequences, and dimension shifting
(`Hartshorne.isRightAcyclic_of_shortExact_injective`) gives the vanishing.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Hartshorne

variable {X : TopCat.{u}}

/-- In an irreducible space of dimension `0`, the closure of every point is the whole space. -/
theorem closure_singleton_eq_univ_of_irreducible_dim_zero [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 0) (x : X) : closure ({x} : Set X) = Set.univ := by
  have hmax := (Order.krullDim_nonpos_iff_forall_isMax).1 hdim.le
  let Z : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hZT : Z ≤ T := fun _ _ => Set.mem_univ _
  exact Set.eq_univ_of_univ_subset (hmax Z hZT)

/-- In an irreducible space of dimension `0`, the only open subsets are `∅` and the whole
space. -/
theorem opens_eq_bot_or_top_of_irreducible_dim_zero [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 0) (U : Opens X) : U = ⊥ ∨ U = ⊤ := by
  by_cases hU : (U : Set X).Nonempty
  · obtain ⟨x, hx⟩ := hU
    right
    ext y
    simp only [Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
    have hxy : x ∈ closure ({y} : Set X) := by
      rw [closure_singleton_eq_univ_of_irreducible_dim_zero hdim y]; exact Set.mem_univ _
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.1 hxy U U.isOpen hx
    rwa [Set.mem_singleton_iff.1 hz] at hzU
  · left
    ext y
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false, SetLike.mem_coe]
    exact fun hy => hU ⟨y, hy⟩

/-- On an irreducible space of dimension `0`, every abelian sheaf is flasque. -/
theorem isFlasque_of_irreducible_dim_zero [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 0) (F : TopCat.Sheaf AddCommGrpCat.{u} X) : F.IsFlasque where
  epi {U V} i := by
    rcases opens_eq_bot_or_top_of_irreducible_dim_zero hdim V.unop with hV | hV
    · have hZ : IsZero (F.obj.obj V) := by
        have h := F.isTerminalOfEqEmpty hV
        exact h.isZero
      exact hZ.epi _
    · rcases opens_eq_bot_or_top_of_irreducible_dim_zero hdim U.unop with hU | hU
      · have hle : V.unop ≤ U.unop := leOfHom i.unop
        rw [hU, hV] at hle
        exact absurd hle (by simp)
      · obtain ⟨U⟩ := U
        obtain ⟨V⟩ := V
        dsimp at hU hV
        subst hU hV
        have : i = 𝟙 _ := Subsingleton.elim _ _
        subst this
        rw [F.obj.map_id]
        infer_instance

/-- On an irreducible space of dimension `0`, the global section functor sends every short
exact sequence of abelian sheaves to a surjection on global sections. -/
theorem epi_map_g_of_irreducible_dim_zero [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 0) {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) : Epi ((sheafSectionsOver (X := X) ⊤).map S.g) := by
  have := isFlasque_of_irreducible_dim_zero hdim S.X₁
  exact TopCat.Sheaf.IsFlasque.epi_of_shortExact hS

/-- On an irreducible space of dimension `0`, the global section functor preserves
epimorphisms. -/
theorem preservesEpimorphisms_sheafSectionsOver_top_of_irreducible_dim_zero [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 0) : (sheafSectionsOver (X := X) ⊤).PreservesEpimorphisms where
  preserves {F G} g _ := by
    let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel (kernelIsKernel g))
        (inferInstanceAs (Mono (kernel.ι g))) (inferInstanceAs (Epi g))
    exact epi_map_g_of_irreducible_dim_zero hdim hS

/-- **Global sections are exact** on an irreducible space of dimension `0` (Hartshorne III.2,
proof of Theorem 2.7, Step 2): `Γ(X,-)` preserves finite colimits; it preserves finite limits
for every space (`Hartshorne.sheafSectionsOver_preservesFiniteLimits`). -/
theorem preservesFiniteColimits_sheafSectionsOver_top_of_irreducible_dim_zero [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 0) :
    PreservesFiniteColimits (sheafSectionsOver (X := X) ⊤) := by
  have := preservesEpimorphisms_sheafSectionsOver_top_of_irreducible_dim_zero hdim
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (sheafSectionsOver (X := X) ⊤)
  exact (sheafSectionsOver (X := X) ⊤).preservesFiniteColimits_of_preservesHomology

/-- **The irreducible dimension-zero base case** (Hartshorne III.2, proof of Theorem 2.7,
Step 2). If `X` is an irreducible space of dimension `0`, then `H^i(X,F) = 0` for every abelian
sheaf `F` and every `i > 0`, here written `i + 1`. The source's noetherian hypothesis is not
needed. -/
theorem sheafCohomology_isZero_of_irreducible_dim_zero [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 0) (F : TopCat.Sheaf AddCommGrpCat.{u} X) (i : ℕ) :
    IsZero ((sheafCohomology X (i + 1)).obj F) :=
  isRightAcyclic_of_shortExact_injective (sheafSectionsOver (X := X) ⊤) (fun _ => True)
    (fun _ hS _ _ => ⟨trivial, epi_map_g_of_irreducible_dim_zero hdim hS⟩) F trivial i

end Hartshorne
