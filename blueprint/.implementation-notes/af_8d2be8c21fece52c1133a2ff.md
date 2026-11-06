# The Picard group of a ringed space

## Partial progress: the scheme case is proved

The module `Hartshorne.Scheme.PicardGroup` proves everything in this article, sorry-free,
for a scheme `X` (modules `X.Modules`):

- Proposition 6.12, first part: `Hartshorne.isInvertible_moduleSheafTensor` (the tensor
  product of invertible sheaves is invertible).
- Proposition 6.12, second part: `Hartshorne.moduleSheafDualEval` (the evaluation map
  `L ⊗ L^∨ ⟶ 𝒪_X`, `l ⊗ ψ ↦ ψ(l)`), `Hartshorne.moduleSheafDualEval_isIso` and
  `Hartshorne.moduleSheafDualEvalIso` (it is an isomorphism for invertible `L`).
- Supporting facts: `Hartshorne.isInvertible_moduleSheafDual` (the dual of an invertible
  sheaf is invertible), `Hartshorne.structureModule_isInvertible`.
- The group: `AlgebraicGeometry.Scheme.Pic` (the quotient of invertible modules by
  isomorphism), `AlgebraicGeometry.Scheme.Pic.mk`, the instance
  `AlgebraicGeometry.Scheme.Pic.instCommGroup`, and `Pic.mk_eq_mk_iff`, `Pic.mk_mul_mk`
  (multiplication is `⊗`), `Pic.one_eq_mk` (identity is `𝒪_X`), `Pic.inv_mk` (inverse is
  the dual `ℋom(L, 𝒪_X)`).
- The isomorphisms that make the axioms hold, with no coherence data needed:
  `moduleSheafTensorAssoc` (built from trilinear maps on sections, `ModuleSheafTrilinear`,
  and the extensionality lemma `moduleSheafTensor_assoc_hom_ext`), `moduleSheafTensorComm`,
  `moduleSheafUnitTensor`, `moduleSheafTensorIsoOfIso`, `moduleSheafDualIsoOfIso`.
- Local-frame tools: `nonempty_restrict_iso_free_of_isLocalFrame`,
  `isLocallyFreeOfRank_of_isLocalFrame`, `IsLocalFrame.homFrame`, and `tensorIsoHomDual`
  (for invertible `L`, `L ⊗ M ≅ ℋom(L^∨, M)`).

## Why the article is not recorded

The article is stated for a ringed space, but the project's invertibility predicate
(`Scheme.Modules.IsInvertible`), sheaf `ℋom`, dual and the duality isomorphisms used here are
defined only for schemes. The tensor product (`moduleSheafTensor`) is already stated for a
sheaf of commutative rings on a topological space. Recording the scheme-level declarations
would weaken the stated generality, and downstream articles (for example
`Pic X ≅ H^1(X, 𝒪_X^*)` for ringed spaces) need the general version.

## Next route

- Either generalize the prerequisites to `SheafOfModules (ringCatSheafOf R)` for a sheaf `R`
  of commutative rings on a topological space: invertible and locally free modules (via
  restriction to opens), sheaf `ℋom` and the dual, and the double-dual and dual-tensor
  isomorphisms. The proofs in `Hartshorne.Scheme.PicardGroup` use only open restriction,
  local frames, stalks and the tensor universal property, so they should carry over.
- Or split the article into a scheme version, which the existing module proves in full, and
  a ringed-space version that depends on the generalized prerequisites.

Lean pitfall: `X.sheaf` is a `TopCat.Sheaf` while `moduleSheafTensor` takes a `Sheaf`, so
`rw` and instance search often fail on terms built from `moduleSheafTensor`. Term-mode proofs
and the `X.Modules`-typed abbreviation `modulesTensorObj` avoid this.
