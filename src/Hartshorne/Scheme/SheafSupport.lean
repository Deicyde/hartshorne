/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Supports of sections and sheaves

Hartshorne, *Algebraic Geometry*, Exercise II.1.14 (p. 67).

The support of a section of a sheaf of abelian groups is the set of points at
which its germ is nonzero. This support is closed in the section's domain. The
support of the sheaf itself is the set of points where its stalk is nontrivial.
-/

open CategoryTheory Opposite TopologicalSpace TopCat

universe u

namespace Hartshorne

variable {X : TopCat.{u}}

/-- The support in `U` of a section of an abelian sheaf. -/
def sectionSupport (F : Sheaf AddCommGrpCat X) (U : Opens X)
    (s : F.obj.obj (op U)) : Set U :=
  {x | F.presheaf.germ U x.1 x.2 s ≠ 0}

/-- The support of an abelian sheaf. -/
def sheafSupport (F : Sheaf AddCommGrpCat X) : Set X :=
  {x | Nontrivial (F.presheaf.stalk x)}

/-- The support of a section of an abelian sheaf is closed in its domain. -/
theorem isClosed_sectionSupport (F : Sheaf AddCommGrpCat X) (U : Opens X)
    (s : F.obj.obj (op U)) : IsClosed (sectionSupport F U s) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  simp only [sectionSupport, Set.mem_compl_iff, Set.mem_ofPred_eq, not_ne_iff] at hx
  have hgerm : F.presheaf.germ U x.1 x.2 s = F.presheaf.germ U x.1 x.2 0 := by
    simpa using hx
  obtain ⟨V, hxV, iVU, _, hres⟩ :=
    F.presheaf.germ_eq x.1 x.2 x.2 s 0 hgerm
  have hres0 : F.presheaf.map iVU.op s = 0 := by simpa using hres
  refine ⟨Subtype.val ⁻¹' (V : Set X), ?_,
    V.isOpen.preimage continuous_subtype_val, hxV⟩
  intro y hy
  simp only [sectionSupport, Set.mem_compl_iff, Set.mem_ofPred_eq, not_ne_iff]
  rw [← F.presheaf.germ_res_apply iVU y.1 hy s, hres0, map_zero]

end Hartshorne
